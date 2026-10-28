import Decoupling.Laurent
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.Block

/-!
# Exactness after the product-state stabilization

This is the matrix exactness assertion used with equation (63) of
`notes/main.pdf`.  If the original physical window is exact, adjoining
an identity X block on coordinates `A` and an identity Z block on
coordinates `B` preserves exactness.

The qubit order is `(F₁ ⊕ A) ⊕ B`; the X-check order is `F₀ ⊕ A`;
the Z-generator order is `F₂ ⊕ B`.  This file proves statements about
the matrices and their column images, without introducing quantum-state
semantics for the ancillary factors.
-/

namespace Decoupling.ProductStates

noncomputable section

open Matrix

variable {F₀ F₁ F₂ A B : Type*}
  [Fintype F₁] [Fintype F₂] [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

/-- The stabilized X matrix `(diag(d,I_A),0_B)`. -/
def H_X (d : Matrix F₀ F₁ R) : Matrix (F₀ ⊕ A) ((F₁ ⊕ A) ⊕ B) R :=
  fromCols (fromBlocks d 0 0 1) 0

/-- The stabilized Z-generator matrix: the block column `(d₂ ; 0_A)` and `I_B`. -/
def H_Z_dagger (d₂ : Matrix F₁ F₂ R) : Matrix ((F₁ ⊕ A) ⊕ B) (F₂ ⊕ B) R :=
  fromBlocks (fromRows d₂ 0) 0 0 1

omit [DecidableEq B] in
theorem H_X_mulVec (d : Matrix F₀ F₁ R) (v : ((F₁ ⊕ A) ⊕ B) → R) :
    H_X d *ᵥ v = Sum.elim (d *ᵥ (fun i => v (.inl (.inl i))))
      (fun a => v (.inl (.inr a))) := by
  simp [H_X, fromBlocks_mulVec, Function.comp_def]

omit [Fintype F₁] [Fintype A] [DecidableEq A] in
theorem H_Z_dagger_mulVec (d₂ : Matrix F₁ F₂ R) (z : (F₂ ⊕ B) → R) :
    H_Z_dagger (A := A) d₂ *ᵥ z =
      Sum.elim (Sum.elim (d₂ *ᵥ (z ∘ Sum.inl)) 0) (z ∘ Sum.inr) := by
  simp [H_Z_dagger, fromBlocks_mulVec]

/-- Stabilization preserves `ker H_X = im H_Z†`, with both ancilla blocks explicit. -/
theorem exactness (d : Matrix F₀ F₁ R) (d₂ : Matrix F₁ F₂ R)
    (hexact : ∀ v, d *ᵥ v = 0 ↔ ∃ z, d₂ *ᵥ z = v)
    (v : ((F₁ ⊕ A) ⊕ B) → R) :
    H_X d *ᵥ v = 0 ↔ ∃ z, H_Z_dagger d₂ *ᵥ z = v := by
  constructor
  · intro h
    rw [H_X_mulVec] at h
    have hd : d *ᵥ (fun i => v (.inl (.inl i))) = 0 := by
      funext i
      exact congrFun h (.inl i)
    have ha : (fun a => v (.inl (.inr a))) = 0 := by
      funext a
      exact congrFun h (.inr a)
    obtain ⟨z, hz⟩ := (hexact _).mp hd
    refine ⟨Sum.elim z (v ∘ Sum.inr), ?_⟩
    rw [H_Z_dagger_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, hz]
    funext i
    rcases i with (i | a) | b
    · rfl
    · exact (congrFun ha a).symm
    · rfl
  · rintro ⟨z, rfl⟩
    rw [H_X_mulVec, H_Z_dagger_mulVec]
    have hd : d *ᵥ (d₂ *ᵥ (z ∘ Sum.inl)) = 0 :=
      (hexact _).mpr ⟨z ∘ Sum.inl, rfl⟩
    simpa only [Sum.elim_inl, Sum.elim_inr, hd] using
      (show Sum.elim (0 : F₀ → R) (0 : A → R) = 0 by
        funext i
        cases i <;> rfl)

end
end Decoupling.ProductStates
