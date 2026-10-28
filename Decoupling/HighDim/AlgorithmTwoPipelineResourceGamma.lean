import Decoupling.HighDim.AlgorithmTwoInputGrowth
import Decoupling.HighDim.AlgorithmTwoPipelineGamma

/-!
# Actual stored comparison stage within the common resource polynomial

Every size premise is discharged from the original bounded input and the
same stored cohomology output. No intermediate rank/radius certificate
is accepted as an input.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipelineResource
open AlgorithmTwoPipeline AlgorithmTwoResourceBudget AlgorithmTwoInputGrowth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
  (inp : Input (D := D) (L := L) (h := h) coords) (hDL : D ≤ L)
  (out : InputLayers coords inp hDL)

omit [DecidableEq K] [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)] in
theorem original_rank_layer :
    inputRank coords L ≤ layer D (inputBudget (L := L) (h := h) coords) :=
  (total_rank_le coords).trans (input_le_layer D _)

theorem gamma_radius :
    gammaRadius coords inp hDL out ≤ comparison D (inputBudget (L := L) (h := h) coords) := by
  rw [comparison_eq]
  exact AlgorithmTwoComparisonGrowth.resultBox_le (original_rank_layer coords)
    (toric_rank coords inp hDL out) (toric_copies coords inp hDL out) (common_radius coords inp hDL out)

theorem gamma_cost (target : StoredTarget coords inp hDL out) :
    (gammaProgram coords inp hDL out target).cost ≤ comparison D (inputBudget (L := L) (h := h) coords) := by
  rw [comparison_eq]
  apply (gammaProgram_cost coords inp hDL out target).trans
  simpa only [pow_two] using AlgorithmTwoComparisonGrowth.comparisonCost_le
    (original_rank_layer (D := D) (h := h) coords) (toric_rank coords inp hDL out)
    (toric_copies coords inp hDL out) (common_radius coords inp hDL out)

theorem comparison_input_radius :
    max out.commonRadius (gammaRadius coords inp hDL out) ≤
      comparison D (inputBudget (L := L) (h := h) coords) :=
  max_le ((common_radius coords inp hDL out).trans (layer_le_comparison D _))
    (gamma_radius coords inp hDL out)

omit [DecidableEq K] [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)] in
theorem original_rank_comparison :
    inputRank coords L ≤ comparison D (inputBudget (L := L) (h := h) coords) :=
  (original_rank_layer coords).trans (layer_le_comparison D _)

theorem toric_rank_comparison :
    AlgorithmTwoToricData.totalRank D out.multiplicities ≤
      comparison D (inputBudget (L := L) (h := h) coords) :=
  (toric_rank coords inp hDL out).trans (layer_le_comparison D _)

/-- Radius of the actual homogeneous cone solve at the shared max box. -/
theorem homotopy_radius_numeric :
    AlgorithmTwoLinearComparison.resultBox D
      (AlgorithmTwoToricData.totalRank D out.multiplicities+inputRank coords L)
      (AlgorithmTwoToricData.totalRank D out.multiplicities+inputRank coords L) 0
      (max out.commonRadius (gammaRadius coords inp hDL out)) ≤
      cone D (inputBudget (L := L) (h := h) coords) := by
  rw [cone_eq]
  exact AlgorithmTwoComparisonGrowth.cone_resultBox_le
    (toric_rank_comparison coords inp hDL out) (original_rank_comparison coords)
    (comparison_input_radius coords inp hDL out)

/-- Includes signed cone assembly, its actual solve, and the negative
block used to materialize the target homotopy. -/
theorem cone_cost_numeric :
    let NT := AlgorithmTwoToricData.totalRank D out.multiplicities
    let NC := inputRank coords L
    let R := max out.commonRadius (gammaRadius coords inp hDL out)
    NT*NT*LaurentArithmetic.boxSize D R +
      AlgorithmTwoLinearComparison.costBound D (NT+NC) (NT+NC) 0 R +
      NC*NC*LaurentArithmetic.boxSize D (AlgorithmTwoLinearComparison.resultBox D (NT+NC) (NT+NC) 0 R) ≤
      cone D (inputBudget (L := L) (h := h) coords) := by
  rw [cone_eq]
  exact AlgorithmTwoComparisonGrowth.coneCost_le
    (toric_rank_comparison coords inp hDL out) (original_rank_comparison coords)
    (comparison_input_radius coords inp hDL out)

theorem c4_radius_numeric :
    max (max out.commonRadius (gammaRadius coords inp hDL out))
      (AlgorithmTwoLinearComparison.resultBox D
        (AlgorithmTwoToricData.totalRank D out.multiplicities+inputRank coords L)
        (AlgorithmTwoToricData.totalRank D out.multiplicities+inputRank coords L) 0
        (max out.commonRadius (gammaRadius coords inp hDL out))) ≤
      cone D (inputBudget (L := L) (h := h) coords) :=
  max_le ((comparison_input_radius coords inp hDL out).trans (comparison_le_cone D _))
    (homotopy_radius_numeric coords inp hDL out)

end Decoupling.HighDim.AlgorithmTwoPipelineResource
