import Decoupling.HighDim.GluedExact
import Mathlib.Tactic.LinearCombination

/-!
# The actual six-qudit glued CSS code

Source: Section V, equation `eq:glued-example` (HD008).
Rows and columns have exactly the displayed order 1,2,3;12,13,23.
Both boxed couplings have their stated signs over arbitrary characteristic.
-/

namespace Decoupling.HighDim.Glued

open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type*) [CommRing K]

def xChecks : Matrix (Fin 4) (Fin 6) (Laurent K 3) :=
  let w := difference K
  ![![w 0, w 1, w 2, -1, 0, 0],
    ![0, 0, 0, -w 1, -w 2, 0],
    ![0, 0, 0, w 0, 0, -w 2],
    ![0, 0, 0, 0, w 0, w 1]]

def zGenerators : Matrix (Fin 6) (Fin 4) (Laurent K 3) :=
  let w := difference K
  ![![-w 1, -w 2, 0, 0],
    ![w 0, 0, -w 2, 0],
    ![0, w 0, w 1, 1],
    ![0, 0, 0, w 2],
    ![0, 0, 0, -w 1],
    ![0, 0, 0, w 0]]

def checks : CSS.Checks K 3 6 4 4 where
  H_X := xChecks K
  H_Z := dagger (zGenerators K)

@[simp] theorem checks_X : (checks K).H_X = xChecks K := rfl
@[simp] theorem checks_Z_dagger : dagger (checks K).H_Z = zGenerators K := dagger_dagger _

theorem commute : xChecks K * zGenerators K = 0 := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [xChecks, zGenerators, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

variable [IsDomain K]

/-- The first topological equality follows from actual Koszul exactness. -/
theorem exact_X (v : Fin 6 → Laurent K 3) :
    xChecks K *ᵥ v = 0 ↔ ∃ z, zGenerators K *ᵥ z = v := by
  constructor
  · intro hv
    have h0 := congrFun hv 0
    have h1 := congrFun hv 1
    have h2 := congrFun hv 2
    have h3 := congrFun hv 3
    simp [xChecks, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at h0 h1 h2 h3
    have hp : secondBoundary (Laurent K 3) (difference K) *ᵥ ![v 3, v 4, v 5] = 0 := by
      funext i
      fin_cases i
      · simpa [secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h1
      · simpa [secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h2
      · simpa [secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h3
    obtain ⟨t, ht⟩ := (second_exact K _).mp hp
    have ht0 := congrFun ht 0
    have ht1 := congrFun ht 1
    have ht2 := congrFun ht 2
    simp [thirdBoundary, Matrix.mulVec, dotProduct] at ht0 ht1 ht2
    have he : firstBoundary (Laurent K 3) (difference K) *ᵥ
        ![v 0, v 1, v 2 - t 0] = 0 := by
      funext i
      fin_cases i
      simp [firstBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
      linear_combination h0 - ht0
    obtain ⟨u, hu⟩ := (first_exact K _).mp he
    have hu0 := congrFun hu 0
    have hu1 := congrFun hu 1
    have hu2 := congrFun hu 2
    simp [secondBoundary, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] at hu0 hu1 hu2
    refine ⟨![u 0, u 1, u 2, t 0], ?_⟩
    funext i
    fin_cases i <;> simp [zGenerators, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
    · exact hu0
    · exact hu1
    · linear_combination hu2
    · exact ht0
    · exact ht1
    · exact ht2
  · rintro ⟨z, rfl⟩
    rw [Matrix.mulVec_mulVec, commute, Matrix.zero_mulVec]

end
end Decoupling.HighDim.Glued
