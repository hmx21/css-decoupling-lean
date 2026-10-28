import Decoupling.HighDim.AlgorithmTwoPipelineResourceLift
import Decoupling.HighDim.AlgorithmTwoPhysicalTransportAncillas

/-! # The actual physical ancilla counts and compiled depth obey the common bound
The counts refer to the identity blocks and product states of the physical
adapter. C4 free check rows are included in the check ranks before this
physical stabilization; they are not counted as extra qudits twice.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipelineResource
open AlgorithmTwoPipeline AlgorithmTwoResourceBudget AlgorithmTwoInputGrowth
open StableFree.Effective.CochainProgram AlgorithmTwoPhysicalTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
  (inp : Input (D := D) (L := L) (h := h) coords) (hDL : D ≤ L)
  (out : InputLayers coords inp hDL)
  (arrays : NativeArrays K D (inputRank coords L)
    (AlgorithmTwoToricData.totalRank D out.multiplicities) (nativeRadius coords inp hDL out))

theorem actual_source_ancillas :
    sourceAncillaCount (coords.rank 1+extraC coords inp hDL out arrays)
      ((targetOriginal coords inp hDL out).rank 0)
      ((targetOriginal coords inp hDL out).rank 1+extraT coords inp hDL out arrays) ≤
      bound D L (inputBudget (L := L) (h := h) coords)  := by
  simpa only [sourceAncillaCount,sourcePlusCount,sourceZeroCount,Fintype.card_fin,Fintype.card_sum] using
    (source_ancilla_count coords inp hDL out arrays).trans (lift_le_bound D L _)

theorem actual_target_ancillas :
    targetAncillaCount (coords.rank 0) (coords.rank 1+extraC coords inp hDL out arrays)
      ((targetOriginal coords inp hDL out).rank 1+extraT coords inp hDL out arrays) ≤
      bound D L (inputBudget (L := L) (h := h) coords)  := by
  simpa only [targetAncillaCount,targetPlusCount,targetZeroCount,Fintype.card_fin,Fintype.card_sum] using
    (target_ancilla_count coords inp hDL out arrays).trans (lift_le_bound D L _)

theorem actual_theta_depth (w : LiftOutput coords inp hDL out arrays) :
    (DenseCircuitPermutation.canonicalThetaProgram w.psiHat w.phiHat).value.length ≤
      bound D L (inputBudget (L := L) (h := h) coords) :=
  (output_theta_depth coords inp hDL out arrays w).trans (lift_le_bound D L _)

end Decoupling.HighDim.AlgorithmTwoPipelineResource
