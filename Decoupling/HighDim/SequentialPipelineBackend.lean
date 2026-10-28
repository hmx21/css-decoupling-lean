import Decoupling.HighDim.AlgorithmTwoPipelineBackend
import Decoupling.HighDim.AlgorithmTwoPipelineBackendData
import Decoupling.HighDim.AlgorithmTwoPipelineExpansion
import Decoupling.HighDim.SequentialProgram

/- HD016: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of Algorithm 2”.
New sequential-contraction execution; historical AlgorithmTwoPipelineBackend is preserved. -/
/-!
# Closed executable Algorithm 2 on finite ranks and coefficient arrays

Only RawInput data and proposition proofs are arguments. The explicit
expansion list removes native C/coordinate objects from the runtime path.
It changes no algorithm: `execute_eq_program` identifies the complete
Work object, including its trace, by reflexivity. Runtime let sharing is
preserved by the elaborator (no zeta reduction); Work.bind itself is not
expanded, preserving call-by-value sharing of every field computation.
The zero-rank guard precedes all box work.
-/
namespace Decoupling.HighDim.SequentialBackend
open AlgorithmTwoPipeline AlgorithmTwoPipelineBackend AlgorithmTwo
open SequentialPipeline
open CategoryTheory HomologicalComplex Matrix ArithmeticCost LaurentArithmetic
open AlgorithmTwoPipeline
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 12000000
attribute [local instance] HasDerivedCategory.standard
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}

/-- Ordinary computable definition. The expansion is solely of the listed
original definitions and generated structure projections. -/
def execute (raw : RawInput K D L h) (valid : Valid raw) (hDL : D ≤ L) : Work K (RuntimeOutput K D) :=
  have sq : SquareZero raw := Classical.choose valid
  have hf : Formal raw sq := Classical.choose_spec valid
  expand_runtime% [SequentialAlgorithmTwo.program, AlgorithmTwoOriginalArrays.Input.program,
    AlgorithmTwoOriginalArrays.Input.toPipeline, AlgorithmTwoOriginalArrays.Input.differential,
    originalInput, coordinates, StableFree.Coordinates.rank,
    Input.differential, StoredLayers.data, StoredTarget.differential, StoredTarget.top,
    StoredGamma.matrix, SequentialPipeline.StoredHomotopy.matrix, SequentialPipeline.StoredExtraction.arrays, SequentialPipeline.StoredStable.arrays,
    SequentialPipeline.Stages.layers, SequentialPipeline.Stages.target, SequentialPipeline.Stages.gamma, SequentialPipeline.Stages.homotopy, SequentialPipeline.Stages.extraction, SequentialPipeline.Stages.stable,
    inputRank, sliceAt, incoming, outgoing, layerProgram, storedLayersProgram,
    StoredLayers.multiplicities, StoredLayers.result, StoredLayers.commonRadius, computeLayers,
    localCocycleColumn, columnAt, cocycleColumns, targetCocycles, storeTargetProgram,
    prepareComparison, gammaRadius, gammaProgram, coneRank, coneRadius, SequentialPipeline.homotopyRadius,
    SequentialPipeline.c4Radius, prepareCone, SequentialPipeline.homotopyProgram, SequentialPipeline.extractionProgram, SequentialPipeline.targetRank, SequentialPipeline.nativeArrays,
    SequentialPipeline.stableProgram, SequentialPipeline.nativeTargetTail, SequentialPipeline.nativeOriginalTail, SequentialPipeline.stableExtraC, SequentialPipeline.stableExtraT, SequentialPipeline.stableBox,
    SequentialPipeline.storeStableProgram, SequentialPipeline.liftProgram, SequentialPipeline.stagesProgram, SequentialPipeline.finishProgram, SequentialPipeline.nonzeroProgram,
    integerSlot, originalSelector, originalSelectors]
    (SequentialAlgorithmTwo.program (coordinates raw sq) (originalInput raw sq hf) hDL)

/-- Equality of the actual returned coefficient-derived word and all recorded
field operations, not merely observational equivalence or equal costs. -/
theorem execute_eq_program (raw : RawInput K D L h) (valid : Valid raw) (hDL : D ≤ L) :
    execute raw valid hDL =
      SequentialAlgorithmTwo.program (coordinates raw (Classical.choose valid))
        (originalInput raw (Classical.choose valid) (Classical.choose_spec valid)) hDL := rfl

end Decoupling.HighDim.SequentialBackend
