import Decoupling.HighDim.CohomologyRelations

/-! # HD012 relation systems with the executable solver's finite column labels -/
namespace Decoupling.HighDim.CohomologyPresentation
open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {D m q g t : ℕ}
  (b : Matrix (Fin q) (Fin m) (Laurent K D))
  (W : Matrix (Fin q) (Fin g) (Laurent K D))

def indexedRelationSystem : Matrix (Fin q) (Fin (g + m)) (Laurent K D) :=
  (relationSystem b W).submatrix id finSumFinEquiv.symm

def indexedRelationProjection (V : Matrix (Fin (g + m)) (Fin t) (Laurent K D)) :
    Matrix (Fin g) (Fin t) (Laurent K D) :=
  V.submatrix (fun i => finSumFinEquiv (Sum.inl i)) id

theorem indexedRelationSystem_mulVec (z : Fin (g + m) → Laurent K D) :
    indexedRelationSystem b W *ᵥ z =
      W *ᵥ (fun j => z (finSumFinEquiv (Sum.inl j))) -
        b *ᵥ (fun j => z (finSumFinEquiv (Sum.inr j))) := by
  rw [indexedRelationSystem, Matrix.submatrix_mulVec_equiv]
  exact relationSystem_mulVec b W (z ∘ finSumFinEquiv)

theorem indexedRelationProjection_range
    (V : Matrix (Fin (g + m)) (Fin t) (Laurent K D))
    (hV : V.mulVecLin.range = (indexedRelationSystem b W).mulVecLin.ker) :
    (indexedRelationProjection V).mulVecLin.range = relations b W := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    have hz : V *ᵥ u ∈ (indexedRelationSystem b W).mulVecLin.ker := by
      rw [← hV]
      exact ⟨u, rfl⟩
    change indexedRelationSystem b W *ᵥ (V *ᵥ u) = 0 at hz
    rw [indexedRelationSystem_mulVec, sub_eq_zero] at hz
    change ∃ z, b *ᵥ z = W *ᵥ (indexedRelationProjection V *ᵥ u)
    exact ⟨fun j => (V *ᵥ u) (finSumFinEquiv (Sum.inr j)), hz.symm⟩
  · rintro ⟨z, hz⟩
    let x : Fin (g + m) → Laurent K D := Sum.elim y z ∘ finSumFinEquiv.symm
    have hx : x ∈ (indexedRelationSystem b W).mulVecLin.ker := by
      change indexedRelationSystem b W *ᵥ x = 0
      rw [indexedRelationSystem_mulVec]
      simp only [x, Function.comp_def, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
      exact sub_eq_zero.mpr hz.symm
    rw [← hV] at hx
    obtain ⟨u, hu⟩ := hx
    refine ⟨u, ?_⟩
    funext i
    change (V *ᵥ u) (finSumFinEquiv (Sum.inl i)) = y i
    have he := congrFun hu (finSumFinEquiv (Sum.inl i))
    simpa only [Matrix.mulVecLin_apply, x, Function.comp_def,
      Equiv.symm_apply_apply, Sum.elim_inl] using he

end
end Decoupling.HighDim.CohomologyPresentation
