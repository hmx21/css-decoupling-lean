import Decoupling.HighDim.AlgorithmTwoPipelineBackendData
import Decoupling.HighDim.AlgorithmTwoPipelineExpansion
import Decoupling.HighDim.AlgorithmTwoProgram

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
namespace Decoupling.HighDim.AlgorithmTwoPipelineBackend
open CategoryTheory HomologicalComplex Matrix ArithmeticCost LaurentArithmetic
open AlgorithmTwoPipeline
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 12000000
attribute [local instance] HasDerivedCategory.standard
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}

def Formal (raw : RawInput K D L h) (sq : SquareZero raw) : Prop :=
  ∃ old : Fin (D-1) → ℕ,
    Nonempty (DerivedCategory.Q.obj (Toric.stackModel K D (Toric.copyForms D old)) ≅
      DerivedCategory.Q.obj (nativeComplex raw sq))

/-- Original complex validity and split profile, with no intermediate solver
or comparison object supplied. Both components are propositions. -/
def Valid (raw : RawInput K D L h) : Prop := ∃ sq : SquareZero raw, Formal raw sq

noncomputable def originalInput (raw : RawInput K D L h) (sq : SquareZero raw) (hf : Formal raw sq) :
    AlgorithmTwoOriginalArrays.Input (L := L) (h := h) (coordinates raw sq) where
  differential := raw.differential
  represents := adjacent_native raw sq
  formal := hf

/-- Ordinary computable definition. The expansion is solely of the listed
original definitions and generated structure projections. -/
def execute (raw : RawInput K D L h) (valid : Valid raw) (hDL : D ≤ L) : Work K (RuntimeOutput K D) :=
  have sq : SquareZero raw := Classical.choose valid
  have hf : Formal raw sq := Classical.choose_spec valid
  expand_runtime% [AlgorithmTwo.program, AlgorithmTwoOriginalArrays.Input.program,
    AlgorithmTwoOriginalArrays.Input.toPipeline, AlgorithmTwoOriginalArrays.Input.differential,
    originalInput, coordinates, StableFree.Coordinates.rank,
    Input.differential, StoredLayers.data, StoredTarget.differential, StoredTarget.top,
    StoredGamma.matrix, StoredHomotopy.matrix, StoredExtraction.arrays, StoredStable.arrays,
    Stages.layers, Stages.target, Stages.gamma, Stages.homotopy, Stages.extraction, Stages.stable,
    inputRank, sliceAt, incoming, outgoing, layerProgram, storedLayersProgram,
    StoredLayers.multiplicities, StoredLayers.result, StoredLayers.commonRadius, computeLayers,
    localCocycleColumn, columnAt, cocycleColumns, targetCocycles, storeTargetProgram,
    prepareComparison, gammaRadius, gammaProgram, coneRank, coneRadius, homotopyRadius,
    c4Radius, prepareCone, homotopyProgram, extractionProgram, targetRank, nativeArrays,
    stableProgram, nativeTargetTail, nativeOriginalTail, stableExtraC, stableExtraT, stableBox,
    storeStableProgram, liftProgram, stagesProgram, finishProgram, nonzeroProgram,
    integerSlot, originalSelector, originalSelectors]
    (AlgorithmTwo.program (coordinates raw sq) (originalInput raw sq hf) hDL)

/-- Equality of the actual returned coefficient-derived word and all recorded
field operations, not merely observational equivalence or equal costs. -/
theorem execute_eq_program (raw : RawInput K D L h) (valid : Valid raw) (hDL : D ≤ L) :
    execute raw valid hDL =
      AlgorithmTwo.program (coordinates raw (Classical.choose valid))
        (originalInput raw (Classical.choose valid) (Classical.choose_spec valid)) hDL := rfl

end Decoupling.HighDim.AlgorithmTwoPipelineBackend
