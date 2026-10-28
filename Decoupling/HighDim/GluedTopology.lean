import Decoupling.HighDim.GluedCode
import Decoupling.HighDim.GluedDualExact

/-!
# Both topological equalities for the actual glued example

The two boxed couplings are included throughout. The second equality
uses the signed dual Koszul exactness, valid also in odd characteristic.
-/

namespace Decoupling.HighDim.Glued

open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [CommRing K] [IsDomain K]

theorem exact_Z (v : Fin 6 → Laurent K 3) :
    dagger (zGenerators K) *ᵥ v = 0 ↔ ∃ z, dagger (xChecks K) *ᵥ z = v := by
  constructor
  · intro hv
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    have h2 := congrFun hv 2
    have h3 := congrFun hv 3
    simp [dagger, zGenerators, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2 h3
    have he : dagger (secondBoundary (Laurent K 3) (difference K)) *ᵥ
        ![v 0, v 1, v 2] = 0 := by
      funext i
      fin_cases i
      · simpa [dagger, secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h0
      · simpa [dagger, secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h1
      · simpa [dagger, secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h2
    obtain ⟨s, hs⟩ := (first_dual_exact K _).mp he
    have hs0 := congrFun hs 0
    have hs1 := congrFun hs 1
    have hs2 := congrFun hs 2
    simp [dagger, firstBoundary, Matrix.mulVec, dotProduct] at hs0 hs1 hs2
    have hp : dagger (thirdBoundary (Laurent K 3) (difference K)) *ᵥ
        ![v 3 + s 0, v 4, v 5] = 0 := by
      funext i
      fin_cases i
      simp [dagger, thirdBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      linear_combination h3 + hs2
    obtain ⟨u, hu⟩ := (second_dual_exact K _).mp hp
    have hu0 := congrFun hu 0
    have hu1 := congrFun hu 1
    have hu2 := congrFun hu 2
    simp [dagger, secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hu0 hu1 hu2
    refine ⟨![s 0, u 0, u 1, u 2], ?_⟩
    funext i
    fin_cases i <;> simp [dagger, xChecks, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · exact hs0
    · exact hs1
    · exact hs2
    · linear_combination hu0
    · exact hu1
    · exact hu2
  · rintro ⟨z, rfl⟩
    rw [Matrix.mulVec_mulVec, ← dagger_mul, commute]
    simp

theorem topological : (checks K).Topological := by
  constructor
  · ext v
    change xChecks K *ᵥ v = 0 ↔ ∃ z, dagger (checks K).H_Z *ᵥ z = v
    rw [checks_Z_dagger]
    exact exact_X K v
  · ext v
    exact exact_Z K v

end
end Decoupling.HighDim.Glued
