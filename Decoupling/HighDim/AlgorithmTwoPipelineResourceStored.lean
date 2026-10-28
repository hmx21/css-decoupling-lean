import Decoupling.HighDim.AlgorithmTwoPipelineResourceC4
import Decoupling.HighDim.AlgorithmTwoPipelineResourceLift
import Decoupling.HighDim.AlgorithmTwoPipelineStableOutput

/-! # Stored C4 and lift stage bounds with every intermediate premise discharged -/
namespace Decoupling.HighDim.AlgorithmTwoPipelineResource
open AlgorithmTwoPipeline AlgorithmTwoResourceBudget AlgorithmTwoInputGrowth ArithmeticCost
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
  (H : StoredHomotopy coords inp hDL out target gamma)
  (x : StoredExtraction coords inp hDL out target gamma H)

theorem stored_stable_cost :
    (storeStableProgram coords inp hDL out target gamma H x).cost ≤
      stable D L (inputBudget (L := L) (h := h) coords) := by
  rw [storeStableProgram_cost]
  exact stable_program_cost coords inp hDL out target gamma H x

variable (u : StoredStable coords inp hDL out target gamma H x)

theorem stored_lift_cost : (liftProgram coords inp hDL out target gamma H x u).cost ≤
    lift D L (inputBudget (L := L) (h := h) coords) :=
  output_lift_cost coords inp hDL out (nativeArrays coords inp hDL out target gamma H x) u.arrays
    (storedStable_solvable coords inp hDL out target gamma H x u)

theorem stored_lift_theta_cost :
    (Work.bind (liftProgram coords inp hDL out target gamma H x u) fun w =>
      DenseCircuitPermutation.canonicalThetaProgram w.psiHat w.phiHat).cost ≤
      lift D L (inputBudget (L := L) (h := h) coords) :=
  output_lift_and_theta_cost coords inp hDL out (nativeArrays coords inp hDL out target gamma H x) u.arrays
    (storedStable_solvable coords inp hDL out target gamma H x u)

theorem stored_lift_theta_depth :
    (Work.bind (liftProgram coords inp hDL out target gamma H x u) fun w =>
      DenseCircuitPermutation.canonicalThetaProgram w.psiHat w.phiHat).value.length ≤
      lift D L (inputBudget (L := L) (h := h) coords) :=
  output_lift_and_theta_depth coords inp hDL out (nativeArrays coords inp hDL out target gamma H x) u.arrays
    (storedStable_solvable coords inp hDL out target gamma H x u)

end Decoupling.HighDim.AlgorithmTwoPipelineResource
