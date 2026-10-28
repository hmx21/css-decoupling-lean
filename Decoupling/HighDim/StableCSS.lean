import Decoupling.HighDim.Laurent
import Decoupling.HighDim.Comparison
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Data.Matrix.Block

/-!
# Exactness after the product-state stabilization

This is the matrix exactness assertion used with equation (63) of
`drafts/main.tex`, Sections IV.A--B.  If the original physical window is exact, adjoining
an identity X block on coordinates `A` and an identity Z block on
coordinates `B` preserves exactness.

The qudit order is `(F₁ ⊕ A) ⊕ B`; the X-check order is `F₀ ⊕ A`;
the Z-generator order is `F₂ ⊕ B`.  This file proves statements about
the matrices and their column images, with quantum-state semantics for these factors proved in
`HighDim/ProductStates.lean` over every prime field.
-/

namespace Decoupling.HighDim.StableCSS

noncomputable section

open Matrix

variable {K : Type*} [CommRing K] {D : ℕ}
local notation "R" => Laurent K D

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

variable [Fintype F₀]

omit [Fintype F₀] [Fintype F₁] [Fintype F₂] [Fintype A] [Fintype B] [DecidableEq A] in
theorem dagger_Z (d₂ : Matrix F₁ F₂ R) :
    dagger (H_Z_dagger (A := A) (B := B) d₂) =
      fromBlocks (fromCols (dagger d₂) 0) 0 0 1 := by
  funext i j
  rcases i with i | b <;> rcases j with (j | a) | b' <;>
    simp [H_Z_dagger, dagger, Matrix.one_apply, eq_comm]

omit [Fintype F₀] [Fintype F₁] [Fintype F₂] [Fintype A] [Fintype B] [DecidableEq B] in
theorem dagger_X (d : Matrix F₀ F₁ R) :
    dagger (H_X (A := A) (B := B) d) =
      fromRows (fromBlocks (dagger d) 0 0 1) 0 := by
  funext i j
  rcases i with (i | a) | b <;> rcases j with j | a' <;>
    simp [H_X, dagger, Matrix.one_apply, eq_comm]

omit [Fintype F₀] [Fintype F₂] [DecidableEq A] in
theorem dagger_Z_mulVec (d₂ : Matrix F₁ F₂ R) (v : ((F₁ ⊕ A) ⊕ B) → R) :
    dagger (H_Z_dagger (A := A) (B := B) d₂) *ᵥ v =
      Sum.elim (dagger d₂ *ᵥ (fun i => v (.inl (.inl i)))) (v ∘ Sum.inr) := by
  simp [dagger_Z, fromBlocks_mulVec, Function.comp_def]

omit [Fintype F₁] [Fintype F₂] [Fintype B] [DecidableEq B] in
theorem dagger_X_mulVec (d : Matrix F₀ F₁ R) (v : (F₀ ⊕ A) → R) :
    dagger (H_X (A := A) (B := B) d) *ᵥ v =
      Sum.elim (Sum.elim (dagger d *ᵥ (v ∘ Sum.inl)) (v ∘ Sum.inr)) 0 := by
  simp [dagger_X, fromBlocks_mulVec]

omit [Fintype F₂] in
/-- The second topological equality also survives identity-X and identity-Z ancillas. -/
theorem reverse_exactness (d : Matrix F₀ F₁ R) (d₂ : Matrix F₁ F₂ R)
    (hexact : ∀ v, dagger d₂ *ᵥ v = 0 ↔ ∃ z, dagger d *ᵥ z = v)
    (v : ((F₁ ⊕ A) ⊕ B) → R) :
    dagger (H_Z_dagger d₂) *ᵥ v = 0 ↔ ∃ z, dagger (H_X d) *ᵥ z = v := by
  constructor
  · intro h
    rw [dagger_Z_mulVec] at h
    have hd : dagger d₂ *ᵥ (fun i => v (.inl (.inl i))) = 0 := by
      funext i
      exact congrFun h (.inl i)
    have hb : (v ∘ Sum.inr) = 0 := by
      funext b
      exact congrFun h (.inr b)
    obtain ⟨z, hz⟩ := (hexact _).mp hd
    refine ⟨Sum.elim z (fun a => v (.inl (.inr a))), ?_⟩
    rw [dagger_X_mulVec]
    simp only [Sum.elim_comp_inl, Sum.elim_comp_inr, hz]
    funext i
    rcases i with (i | a) | b
    · rfl
    · rfl
    · exact (congrFun hb b).symm
  · rintro ⟨z, rfl⟩
    rw [dagger_Z_mulVec, dagger_X_mulVec]
    have hd : dagger d₂ *ᵥ (dagger d *ᵥ (z ∘ Sum.inl)) = 0 :=
      (hexact _).mpr ⟨z ∘ Sum.inl, rfl⟩
    simpa only [Sum.elim_inl, Sum.elim_inr, Sum.elim_comp_inr, hd] using
      (show Sum.elim (0 : F₂ → R) (0 : B → R) = 0 by
        funext i
        cases i <;> rfl)

end
end Decoupling.HighDim.StableCSS

namespace Decoupling.HighDim.StableCSS

noncomputable section
open Matrix

variable {R : Type*} [CommRing R]
variable {Q C A : Type*} [Fintype Q] [Fintype C] [Fintype A]

/-- Additional identity-valued checks are zero rows in the polynomial check matrix. -/
def identityChecks (d : Matrix C Q R) : Matrix (C ⊕ A) Q R := fromRows d 0

omit [Fintype C] [Fintype A] in
theorem identityChecks_mulVec (d : Matrix C Q R) (v : Q → R) :
    identityChecks (A := A) d *ᵥ v = Sum.elim (d *ᵥ v) 0 := by
  simp [identityChecks]

omit [Fintype C] [Fintype A] in
/-- Adjoining zero check rows does not change the original physical kernel. -/
theorem identityChecks_kernel (d : Matrix C Q R) (v : Q → R) :
    identityChecks (A := A) d *ᵥ v = 0 ↔ d *ᵥ v = 0 := by
  rw [identityChecks_mulVec]
  constructor
  · intro h
    funext i
    exact congrFun h (.inl i)
  · intro h
    simp [h]

def identityQuotientMap (d : Matrix C Q R) :
    ((C ⊕ A) → R) →ₗ[R] Comparison.CheckCokernel d × (A → R) :=
  ((Comparison.checkQuotient d).comp (LinearMap.funLeft R R Sum.inl)).prod
    (LinearMap.funLeft R R Sum.inr)

omit [Fintype C] [Fintype A] in
theorem identityQuotientMap_surjective (d : Matrix C Q R) :
    Function.Surjective (identityQuotientMap (A := A) d) := by
  rintro ⟨q, a⟩
  obtain ⟨v, hv⟩ := (LinearMap.range d.mulVecLin).mkQ_surjective q
  refine ⟨Sum.elim v a, ?_⟩
  exact Prod.ext hv rfl

omit [Fintype C] [Fintype A] in
theorem identityQuotientMap_kernel (d : Matrix C Q R) :
    LinearMap.ker (identityQuotientMap (A := A) d) =
      LinearMap.range (identityChecks (A := A) d).mulVecLin := by
  ext v
  change identityQuotientMap d v = 0 ↔ ∃ w, identityChecks d *ᵥ w = v
  constructor
  · intro h
    have hq : (LinearMap.range d.mulVecLin).mkQ (v ∘ Sum.inl) = 0 :=
      congrArg Prod.fst h
    have ha : (v ∘ Sum.inr) = 0 := congrArg Prod.snd h
    obtain ⟨w, hw⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
    refine ⟨w, ?_⟩
    rw [identityChecks_mulVec]
    funext i
    cases i with
    | inl c => exact congrFun hw c
    | inr a => exact (congrFun ha a).symm
  · rintro ⟨w, rfl⟩
    apply Prod.ext
    · apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨w, ?_⟩
      funext i
      simp [identityChecks_mulVec]
    · funext a
      simp [identityQuotientMap, identityChecks_mulVec, LinearMap.funLeft]

/-- The actual enlarged cokernel is the original cokernel plus the free
module of identity-valued checks. This proves rather than assumes the absorption step. -/
def identityCheckCokernelEquiv (d : Matrix C Q R) :
    Comparison.CheckCokernel (identityChecks (A := A) d) ≃ₗ[R]
      Comparison.CheckCokernel d × (A → R) :=
  (Submodule.quotEquivOfEq _ _ (identityQuotientMap_kernel (A := A) d).symm).trans
    ((identityQuotientMap d).quotKerEquivOfSurjective (identityQuotientMap_surjective d))

end
end Decoupling.HighDim.StableCSS
namespace Decoupling.HighDim.StableCSS

noncomputable section
open Matrix

variable {K : Type*} [CommRing K] {D : ℕ}
local notation "R" => Laurent K D
variable {Q C Z I A B : Type*}
  [Fintype Q] [Fintype C] [Fintype Z] [Fintype I] [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

omit [Fintype Q] in
theorem identityChecks_dagger_mulVec (d : Matrix C Q R) (v : (C ⊕ I) → R) :
    dagger (identityChecks d) *ᵥ v = dagger d *ᵥ (v ∘ Sum.inl) := by
  have h : dagger (identityChecks (A := I) d) = Matrix.fromCols (dagger d) 0 := by
    ext i j
    cases j <;> simp [dagger, identityChecks]
  rw [h, Matrix.fromCols_mulVec]
  simp

omit [Fintype Q] in
theorem identityChecks_dagger_image (d : Matrix C Q R) (v : Q → R) :
    (∃ z, dagger (identityChecks (A := I) d) *ᵥ z = v) ↔
      ∃ z, dagger d *ᵥ z = v := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z ∘ Sum.inl, (identityChecks_dagger_mulVec d z).symm.trans hz⟩
  · rintro ⟨z, rfl⟩
    exact ⟨Sum.elim z 0, by simp [identityChecks_dagger_mulVec]⟩

/-- Both topological exactness equalities survive zero check rows followed
by identity X and identity Z ancillas. The identities are proved separately;
the reverse topological condition is not discarded. -/
theorem both_exact_after_stabilization
    (d : Matrix C Q R) (z : Matrix Q Z R)
    (hX : ∀ v, d *ᵥ v = 0 ↔ ∃ w, z *ᵥ w = v)
    (hZ : ∀ v, dagger z *ᵥ v = 0 ↔ ∃ w, dagger d *ᵥ w = v) :
    (∀ v : ((Q ⊕ A) ⊕ B) → R,
      H_X (identityChecks (A := I) d) *ᵥ v = 0 ↔
        ∃ w, H_Z_dagger z *ᵥ w = v) ∧
    (∀ v : ((Q ⊕ A) ⊕ B) → R,
      dagger (H_Z_dagger z) *ᵥ v = 0 ↔
        ∃ w, dagger (H_X (identityChecks (A := I) d)) *ᵥ w = v) := by
  constructor
  · apply exactness
    intro v
    exact (identityChecks_kernel d v).trans (hX v)
  · apply reverse_exactness
    intro v
    exact (hZ v).trans (identityChecks_dagger_image d v).symm

end
end Decoupling.HighDim.StableCSS

