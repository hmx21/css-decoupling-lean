import Decoupling.HighDim.AlgorithmTwoOriginalArraysSize
import Decoupling.HighDim.AlgorithmTwoPipelineZero

/-! # The paper's zero coefficient count is exactly the empty-rank case -/
namespace Decoupling.HighDim.AlgorithmTwoOriginalArrays
open AlgorithmTwoPipeline
variable {K : Type} [Field K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]

theorem coefficientCount_zero_of_total_zero (hz : inputRank coords L = 0) :
    coefficientCount (D := D) (L := L) (h := h) coords = 0 := by
  unfold coefficientCount
  apply Finset.sum_eq_zero
  intro i _
  rw [rank_zero_of_total_zero coords hz (-(L:ℤ)+i)]
  simp

/-- The formal profile excludes nonzero isolated free terms in positive
dimension. Thus an input of size zero really can take the empty branch,
even when its formally supplied exponent-box radius is arbitrary. -/
theorem Input.total_zero_iff (inp : Input (L := L) (h := h) coords) (hD : 0 < D) :
    inputRank coords L = 0 ↔ coefficientCount (D := D) (L := L) (h := h) coords = 0 := by
  constructor
  · exact coefficientCount_zero_of_total_zero coords
  · intro hz
    by_contra hn
    have hp : 0 < inputRank coords L := Nat.pos_of_ne_zero hn
    have hb := inp.dense_budget coords hD hp
    rw [hz,mul_zero] at hb
    omega

end Decoupling.HighDim.AlgorithmTwoOriginalArrays
