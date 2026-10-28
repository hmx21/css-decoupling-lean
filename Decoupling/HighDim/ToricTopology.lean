import Decoupling.HighDim.ToricHodgeCoordinates

/-!
# Both actual topological equalities for every internal toric window

The second equality is transported from primal Koszul exactness through
the proved signed Hodge duality and the Laurent antipode. It is not an
extra assumption on the target code. Valid over every coefficient domain.
-/

namespace Decoupling.HighDim.Toric

open Matrix Koszul

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [CommRing K] [IsDomain K] (D k : ℕ)

theorem checks_exact_Z (hk : k + 1 < D) :
    LinearMap.ker (checks K D k).H_Z.mulVecLin =
      LinearMap.range (dagger (checks K D k).H_X).mulVecLin := by
  ext v
  change dagger (boundaryMatrix K D (k + 1)) *ᵥ v = 0 ↔
    ∃ z, dagger (boundaryMatrix K D k) *ᵥ z = v
  constructor
  · intro hv
    let f := (dualCellCoordinates K (k + 1)).symm (barVector K v)
    have hf : (boundary (Laurent K D) (difference K) (k + 1)).hom.dualMap f = 0 := by
      apply (dualCellCoordinates K (k + 2)).injective
      rw [dualCellCoordinates_precomp, map_zero]
      change (boundaryMatrix K D (k + 1)).transpose *ᵥ
        dualCellCoordinates K (k + 1)
          ((dualCellCoordinates K (k + 1)).symm (barVector K v)) = 0
      rw [LinearEquiv.apply_symm_apply, ← barVector_dagger_mulVec, hv]
      ext i
      simp [barVector]
    obtain ⟨g, hg⟩ := Hodge.dual_exact K (by omega : k + (D - k - 2) + 2 = D) f hf
    refine ⟨barVector K (dualCellCoordinates K k g), ?_⟩
    apply barVector_injective K
    rw [barVector_dagger_mulVec, barVector_involutive, ← dualCellCoordinates_precomp, hg]
    exact (dualCellCoordinates K (k + 1)).apply_symm_apply _
  · rintro ⟨z, rfl⟩
    rw [Matrix.mulVec_mulVec, ← dagger_mul]
    have h := checks_commute K D k
    rw [checks_H_X, checks_dagger_H_Z] at h
    rw [h]
    simp

theorem checks_topological (hk : k + 1 < D) : (checks K D k).Topological :=
  ⟨checks_exact_X K D k, checks_exact_Z K D k hk⟩

end
end Decoupling.HighDim.Toric
