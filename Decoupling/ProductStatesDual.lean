import Decoupling.ProductStates

/-!
# Both topological equalities after product-state stabilization

The reverse exactness equality is proved with the same literal ancillary
orders as `ProductStates`, complementing its forward exactness theorem.
-/

namespace Decoupling.ProductStatesDual

open Matrix ProductStates

noncomputable section

variable {F₀ F₁ F₂ A B : Type*}
  [Fintype F₀] [Fintype F₁] [Fintype F₂] [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

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
theorem exactness (d : Matrix F₀ F₁ R) (d₂ : Matrix F₁ F₂ R)
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
end Decoupling.ProductStatesDual
