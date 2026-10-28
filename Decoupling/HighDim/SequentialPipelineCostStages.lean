import Decoupling.HighDim.SequentialPipelineResourceCone
import Decoupling.HighDim.SequentialPipelineResourceLift

/-!
HD016: Appendix C4 “Inverting Γ” and C5 “The lines of Algorithm 2”;
all resources refer to the descending contraction in the new execution.

# Trace sums for the actual stage programs

These helper statements use the same typed stored arrays at each stage.
They are used after expanding the final program's Work.bind trace; they
do not replace that final execution with a proxy algorithm.
-/
namespace Decoupling.HighDim.SequentialPipelineResource
open AlgorithmTwoPipeline SequentialPipeline SequentialResourceBudget AlgorithmTwoInputGrowth
open StableFree.Effective.CochainProgram AlgorithmTwoInvertible ArithmeticCost HomologicalComplex
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

theorem prefix_cost :
    (computeLayers coords inp hDL).cost+(storeTargetProgram coords inp hDL out).cost+
      (gammaProgram coords inp hDL out target).cost+
      (SequentialPipeline.homotopyProgram coords inp hDL out target gamma).cost+
      (SequentialPipeline.extractionProgram coords inp hDL out target gamma H).cost ≤
      1+layer D (inputBudget (L := L) (h := h) coords)+
        comparison D (inputBudget (L := L) (h := h) coords)+
        cone D L (inputBudget (L := L) (h := h) coords) := by
  have hl : (computeLayers coords inp hDL).cost ≤
      layer D (inputBudget (L := L) (h := h) coords) := layers_cost coords inp hDL
  have ht := storeTargetProgram_cost coords inp hDL out
  have hg := gamma_cost coords inp hDL out target
  have hh := cone_program_cost coords inp hDL out target gamma H
  omega

variable (arrays : NativeArrays K D (inputRank coords L)
    (AlgorithmTwoToricData.totalRank D out.multiplicities) (nativeRadius coords inp hDL out))
  [C.IsGE 1]
  [(AlgorithmTwoToricData.nativeStack D out.multiplicities K).IsGE 1]
  [(AlgorithmTwoToricData.nativeStack D out.multiplicities K).IsStrictlyGE (-(L:ℤ))]
  (e : HomotopyEquiv C (AlgorithmTwoToricData.nativeStack D out.multiplicities K))
  (ha : NativeRealizes (inputCoordinates (L := L) coords)
    (AlgorithmTwoToricData.totalCoordinates D out.multiplicities K) e arrays)
  (v : StableOutput coords inp hDL out arrays)
  (hv : FourSolvable (LaurentArithmetic.matrixDenote v.dC) (LaurentArithmetic.matrixDenote v.dT)
    (LaurentArithmetic.matrixDenote v.forward) (LaurentArithmetic.matrixDenote v.inverse))
  (w : LiftOutput coords inp hDL out arrays)

/-- Exact sum of the field-operation traces of all eight actual stages.
The full pipeline theorem specializes these arguments to its stored values. -/
theorem all_stages_cost :
    (computeLayers coords inp hDL).cost+(storeTargetProgram coords inp hDL out).cost+
      (gammaProgram coords inp hDL out target).cost+
      (SequentialPipeline.homotopyProgram coords inp hDL out target gamma).cost+
      (SequentialPipeline.extractionProgram coords inp hDL out target gamma H).cost+
      (execute coords (targetOriginal coords inp hDL out) (inputCoordinates (L := L) coords)
        (AlgorithmTwoToricData.totalCoordinates D out.multiplicities K)
        (originalSelectors (L := L) coords)
        (selectorsFromDegree (AlgorithmTwoToricData.totalCoordinates D out.multiplicities K).degree)
        (originalSelectors_realizes coords) (selectorsFromDegree_realizes _)
        e arrays ha L).cost+
      (liftMatricesProgram v.dC v.dT v.forward v.inverse hv).cost+
      (DenseCircuitPermutation.canonicalThetaProgram w.psiHat w.phiHat).cost ≤
      bound D L (inputBudget (L := L) (h := h) coords) := by
  have hp := prefix_cost coords inp hDL out target gamma H
  have hs := stable_execute_cost coords inp hDL out arrays e ha
  have hl := output_lift_cost coords inp hDL out arrays v hv
  have hw := output_theta_cost coords inp hDL out arrays w
  rw [bound_eq]
  omega

end Decoupling.HighDim.SequentialPipelineResource
