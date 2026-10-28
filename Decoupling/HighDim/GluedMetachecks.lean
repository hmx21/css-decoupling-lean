import Decoupling.HighDim.GluedTopology

/-!
# The actual last X metacheck of the glued example

This proves the complete length-two resolution at the prescribed check
presentation. Its last map is injective, not an assumed syzygy certificate.
-/

namespace Decoupling.HighDim.Glued

open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [CommRing K] [IsDomain K]

def metacheck : Matrix (Fin 1) (Fin 4) (Laurent K 3) :=
  ![![0, difference K 0, difference K 1, difference K 2]]

omit [IsDomain K] in
theorem metacheck_comp : metacheck K * xChecks K = 0 := by
  apply Matrix.ext
  intro i j
  fin_cases i
  fin_cases j <;> simp [metacheck, xChecks, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

theorem metacheck_dagger_injective :
    Function.Injective (dagger (metacheck K)).mulVecLin := by
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have h1 := congrFun hv 1
  simp [metacheck, dagger, Matrix.mulVec, dotProduct] at h1
  have hz := h1.resolve_left (Koszul.difference_ne_zero (K := K) (0 : Fin 3))
  funext i
  fin_cases i
  exact hz

theorem exact_metacheck (v : Fin 4 → Laurent K 3) :
    dagger (xChecks K) *ᵥ v = 0 ↔ ∃ z, dagger (metacheck K) *ᵥ z = v := by
  constructor
  · intro hv
    have h0 := congrFun hv 0
    have h3 := congrFun hv 3
    have h4 := congrFun hv 4
    have h5 := congrFun hv 5
    simp [xChecks, dagger, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h3 h4 h5
    have hz : v 0 = 0 := h0.resolve_left (Koszul.difference_ne_zero (K := K) (0 : Fin 3))
    have he : dagger (secondBoundary (Laurent K 3) (difference K)) *ᵥ
        ![v 1, v 2, v 3] = 0 := by
      funext i
      fin_cases i
      · simpa [dagger, secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hz] using h3
      · simpa [dagger, secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h4
      · simpa [dagger, secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h5
    obtain ⟨s, hs⟩ := (first_dual_exact K _).mp he
    refine ⟨s, ?_⟩
    funext i
    fin_cases i
    · simpa [metacheck, dagger, Matrix.mulVec, dotProduct] using hz.symm
    · simpa [metacheck, dagger, firstBoundary, Matrix.mulVec, dotProduct] using congrFun hs 0
    · simpa [metacheck, dagger, firstBoundary, Matrix.mulVec, dotProduct] using congrFun hs 1
    · simpa [metacheck, dagger, firstBoundary, Matrix.mulVec, dotProduct] using congrFun hs 2
  · rintro ⟨z, rfl⟩
    rw [Matrix.mulVec_mulVec, ← dagger_mul, metacheck_comp]
    simp

end
end Decoupling.HighDim.Glued
