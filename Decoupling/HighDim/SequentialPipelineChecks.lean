import Decoupling.HighDim.AlgorithmTwoPipelineChecks
import Decoupling.HighDim.SequentialPipelineProgram
import Decoupling.HighDim.AlgorithmTwoPhysicalTransportComputed

/- HD016: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of Algorithm 2”.
New sequential-contraction execution; historical AlgorithmTwoPipelineChecks is preserved. -/
/-! # Actual original-coordinate checks and identity rows returned by C4 -/
namespace Decoupling.HighDim.SequentialPipeline
open AlgorithmTwoPipeline
open CategoryTheory HomologicalComplex Matrix ArithmeticCost AlgorithmTwoFiniteComplex
open StableFree.Effective StableFree.Effective.CochainProgram
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
variable {K : Type} [Field K] {D : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}

variable [DecidableEq K] {L h : ℕ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
variable (inp : Input (D := D) (L := L) (h := h) cC) (hDL : D ≤ L)
variable (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
  (g : StoredGamma cC inp hDL s t) (H : StoredHomotopy cC inp hDL s t g)
  (x : StoredExtraction cC inp hDL s t g H) (u : StoredStable cC inp hDL s t g H x)

theorem stable_original_dC : LaurentArithmetic.matrixDenote u.arrays.dC =
    AlgorithmTwoPhysicalTransport.identityChecksOrdinal (degreeMatrix cC 0 1) (stableExtraC cC inp hDL s t g H x) := by
  rw [u.correct]
  change LaurentArithmetic.matrixDenote (augmentedRelations (originalSelectors (L := L) cC)
    (nativeArrays cC inp hDL s t g H x).differentialC _ _) = _
  rw [augmentedRelations_correct _ _ _ (runBox_ge_input _ _ _ _ _)]
  rw [originalSlice_native cC cC (inputCoordinates (L := L) cC) (inputCoordinates (L := L) cC)
    _ _ (originalSelectors_realizes cC) (originalSelectors_realizes cC) 1 0 _ _
    (represents_at _ _ (nativeArrays_realizes cC inp hDL s t g H x).differentialC 0 1 rfl)]
  rfl

theorem stable_original_dT : LaurentArithmetic.matrixDenote u.arrays.dT =
    AlgorithmTwoPhysicalTransport.identityChecksOrdinal
      (degreeMatrix (originalFromFrame (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K)) 0 1)
      (stableExtraT cC inp hDL s t g H x) := by
  rw [u.correct]
  change LaurentArithmetic.matrixDenote (augmentedRelations
    (selectorsFromDegree (AlgorithmTwoToricData.degrees D s.multiplicities))
    (nativeArrays cC inp hDL s t g H x).differentialT _ _) = _
  rw [augmentedRelations_correct _ _ _ (runBox_ge_input _ _ _ _ _)]
  erw [originalSlice_native (originalFromFrame _) (originalFromFrame _)
    (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K) (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K)
    _ _ (selectorsFromDegree_realizes _) (selectorsFromDegree_realizes _) 1 0 _ _
    (represents_at _ _ (nativeArrays_realizes cC inp hDL s t g H x).differentialT 0 1 rfl)]
  rfl

end
end Decoupling.HighDim.SequentialPipeline
