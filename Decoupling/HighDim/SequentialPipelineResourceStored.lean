import Decoupling.HighDim.SequentialPipelineResourceC4
import Decoupling.HighDim.SequentialPipelineResourceLift
import Decoupling.HighDim.SequentialPipelineStableOutput

/-!
HD016: Appendix C4 “Inverting Γ” and C5 “The lines of Algorithm 2”;
all resources refer to the descending contraction in the new execution.
 # Stored C4 and lift stage bounds with every intermediate premise discharged -/
namespace Decoupling.HighDim.SequentialPipelineResource
open AlgorithmTwoPipeline SequentialPipeline SequentialResourceBudget AlgorithmTwoInputGrowth ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
  (inp : Input (D := D) (L := L) (h := h) coords) (hDL : D ≤ L)
  (out : InputLayers coords inp hDL)
  (target : StoredTarget coords inp hDL out)
  (gamma : StoredGamma coords inp hDL out target)
  (H : SequentialPipeline.StoredHomotopy coords inp hDL out target gamma)
  (x : SequentialPipeline.StoredExtraction coords inp hDL out target gamma H)

theorem stored_stable_cost :
    (SequentialPipeline.storeStableProgram coords inp hDL out target gamma H x).cost ≤
      stable D L (inputBudget (L := L) (h := h) coords) := by
  rw [SequentialPipeline.storeStableProgram_cost]
  exact stable_program_cost coords inp hDL out target gamma H x

variable (u : SequentialPipeline.StoredStable coords inp hDL out target gamma H x)

theorem stored_lift_cost : (SequentialPipeline.liftProgram coords inp hDL out target gamma H x u).cost ≤
    lift D L (inputBudget (L := L) (h := h) coords) :=
  output_lift_cost coords inp hDL out (SequentialPipeline.nativeArrays coords inp hDL out target gamma H x) u.arrays
    (SequentialPipeline.storedStable_solvable coords inp hDL out target gamma H x u)

theorem stored_lift_theta_cost :
    (Work.bind (SequentialPipeline.liftProgram coords inp hDL out target gamma H x u) fun w =>
      DenseCircuitPermutation.canonicalThetaProgram w.psiHat w.phiHat).cost ≤
      lift D L (inputBudget (L := L) (h := h) coords) :=
  output_lift_and_theta_cost coords inp hDL out (SequentialPipeline.nativeArrays coords inp hDL out target gamma H x) u.arrays
    (SequentialPipeline.storedStable_solvable coords inp hDL out target gamma H x u)

theorem stored_lift_theta_depth :
    (Work.bind (SequentialPipeline.liftProgram coords inp hDL out target gamma H x u) fun w =>
      DenseCircuitPermutation.canonicalThetaProgram w.psiHat w.phiHat).value.length ≤
      lift D L (inputBudget (L := L) (h := h) coords) :=
  output_lift_and_theta_depth coords inp hDL out (SequentialPipeline.nativeArrays coords inp hDL out target gamma H x) u.arrays
    (SequentialPipeline.storedStable_solvable coords inp hDL out target gamma H x u)

end Decoupling.HighDim.SequentialPipelineResource
