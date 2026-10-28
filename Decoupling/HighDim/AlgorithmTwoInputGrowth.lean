import Decoupling.HighDim.AlgorithmTwoOriginalArraysSize
import Decoupling.HighDim.AlgorithmTwoResourceBudget
import Decoupling.HighDim.AlgorithmTwoToricDataIndex

/-!
# HD012 first-stage bounds from the actual original input

All rank premises of the layer bounds are discharged from the finite
original coordinate window. The stored multiplicities then bound the
actual mask-indexed toric target and the actual common coefficient box.
-/
namespace Decoupling.HighDim.AlgorithmTwoInputGrowth
open AlgorithmTwoPipeline AlgorithmTwoResourceBudget
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]

def inputBudget := inputRank coords L+h

omit [DecidableEq K] [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)] in
theorem total_rank_le : inputRank coords L ≤ inputBudget (L := L) (h := h) coords := by
  unfold inputBudget; omega

omit [DecidableEq K] [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)] in
theorem radius_le : h ≤ inputBudget (L := L) (h := h) coords := by
  unfold inputBudget; omega

omit [DecidableEq K] in
theorem term_rank_le (j : ℤ) : coords.rank j ≤ inputBudget (L := L) (h := h) coords :=
  (AlgorithmInputSize.pipeline_rank_le (L := L) coords j).trans (total_rank_le coords)

variable (inp : Input (D := D) (L := L) (h := h) coords) (hDL : D ≤ L)

theorem layers_cost :
    (computeLayers coords inp hDL).cost ≤ layer D (inputBudget (L := L) (h := h) coords) := by
  exact AlgorithmTwoLayersGrowth.layer_cost_polynomial coords
    (incoming coords inp hDL) (outgoing coords inp hDL) (term_rank_le coords) (radius_le coords)

variable (out : StoredLayers coords (incoming coords inp hDL) (outgoing coords inp hDL))

theorem common_radius :
    out.commonRadius ≤ layer D (inputBudget (L := L) (h := h) coords) := by
  rw [layer_eq]
  exact AlgorithmTwoLayersGrowth.commonRadius_le out (term_rank_le coords) (radius_le coords)

theorem toric_rank :
    AlgorithmTwoToricData.totalRank D out.multiplicities ≤
      layer D (inputBudget (L := L) (h := h) coords) := by
  rw [AlgorithmTwoToricData.totalRank_eq,layer_eq]
  exact AlgorithmTwoLayersGrowth.target_rank_le out (term_rank_le coords) (radius_le coords)

theorem toric_copies :
    AlgorithmTwoToricData.copyCount D out.multiplicities ≤
      layer D (inputBudget (L := L) (h := h) coords) := by
  rw [layer_eq]
  exact AlgorithmTwoLayersGrowth.top_count_le out (term_rank_le coords) (radius_le coords)

include inp in
omit [DecidableEq K] in
theorem original_dense_budget (hD : 0 < D) (hnonzero : 0 < inputRank coords L) :
    inputBudget (L := L) (h := h) coords ≤
      (2*(2*L+1)+1)*AlgorithmInputSize.paperCoefficientCount (D := D) (L := L) (h := h) coords :=
  AlgorithmInputSize.pipeline_dense_budget coords inp hD hnonzero

end Decoupling.HighDim.AlgorithmTwoInputGrowth
