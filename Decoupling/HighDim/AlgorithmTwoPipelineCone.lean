import Decoupling.HighDim.AlgorithmTwoPipelineGamma
import Decoupling.HighDim.AlgorithmTwoPipelineFrame
import Decoupling.HighDim.AlgorithmTwoLinearComparisonExtract
import Decoupling.HighDim.AlgorithmTwoFiniteComplexBlockEquivalence

/-! # The actual cone-contraction solve, using no native map as runtime data -/
namespace Decoupling.HighDim.AlgorithmTwoPipeline
open CategoryTheory HomologicalComplex Matrix ArithmeticCost AlgorithmTwoFiniteComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
variable (inp : Input (D := D) (L := L) (h := h) cC) (hDL : D ≤ L)

abbrev coneRank (s : InputLayers cC inp hDL) := AlgorithmTwoToricData.totalRank D s.multiplicities + inputRank cC L

def coneRadius (s : InputLayers cC inp hDL) : ℕ := max s.commonRadius (gammaRadius cC inp hDL s)

abbrev homotopyRadius (s : InputLayers cC inp hDL) :=
  AlgorithmTwoLinearComparison.resultBox D (coneRank cC inp hDL s) (coneRank cC inp hDL s) 0 (coneRadius cC inp hDL s)

def c4Radius (s : InputLayers cC inp hDL) : ℕ := max (coneRadius cC inp hDL s) (homotopyRadius cC inp hDL s)

def prepareCone (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s) (g : StoredGamma cC inp hDL s t) :
    Work K (LaurentArithmetic.DenseMatrix K D (coneRank cC inp hDL s) (coneRank cC inp hDL s) (coneRadius cC inp hDL s)) :=
  AlgorithmTwoLinearComparison.coneArrayProgram
    (LaurentArithmetic.matrixPad t.differential (coneRadius cC inp hDL s))
    (LaurentArithmetic.matrixPad inp.differential (coneRadius cC inp hDL s))
    (LaurentArithmetic.matrixPad g.matrix (coneRadius cC inp hDL s))

noncomputable section

theorem prepareCone_correct (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
    (g : StoredGamma cC inp hDL s t) :
    LaurentArithmetic.matrixDenote (prepareCone cC inp hDL s t g).value =
      coneMatrix (LaurentArithmetic.matrixDenote t.differential)
        (LaurentArithmetic.matrixDenote inp.differential) (LaurentArithmetic.matrixDenote g.matrix) := by
  rw [prepareCone,AlgorithmTwoLinearComparison.coneArrayProgram_correct]
  erw [LaurentArithmetic.matrixPad_correct t.differential
      (show 1 ≤ coneRadius cC inp hDL s from s.one_le_commonRadius.trans (le_max_left _ _)),
    LaurentArithmetic.matrixPad_correct inp.differential
      (show h ≤ coneRadius cC inp hDL s from s.input_le_commonRadius.trans (le_max_left _ _)),
    LaurentArithmetic.matrixPad_correct g.matrix
      (show gammaRadius cC inp hDL s ≤ coneRadius cC inp hDL s from le_max_right _ _)]
  rfl

theorem cone_solvable (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
    (g : StoredGamma cC inp hDL s t) :
    ∃ H, (AlgorithmTwoLinearComparison.contractionInput (prepareCone cC inp hDL s t g).value
      (coneDegree (AlgorithmTwoToricData.degrees D s.multiplicities)
        (totalDegree cC.rank (-(L:ℤ)) (inputLength L)))).Satisfied H := by
  let f := gammaMap cC inp hDL s t g
  let : QuasiIso f := gammaMap_quasiIso cC inp hDL s t g
  let : (AlgorithmTwoToricData.nativeStack D s.multiplicities K).IsStrictlyLE (D:ℤ) :=
    (AlgorithmTwoToricData.nativeStack_bounds D s.multiplicities K).2
  let ft := AlgorithmTwoToricData.totalCoordinates D s.multiplicities K
  let fc := inputCoordinates (L := L) cC
  let c := Coordinates.cone f ft fc
  let nativeH := AlgorithmTwoComparison.coneContraction f (originalFromFrame ft) cC D L
  have hd : c.RepresentsDifferential (coneMatrix (LaurentArithmetic.matrixDenote t.differential)
      (LaurentArithmetic.matrixDenote inp.differential) (LaurentArithmetic.matrixDenote g.matrix)) :=
    coneMatrix_represents f ft fc _ _ _ (storedTarget_represents cC inp hDL s t) inp.represents
      (gammaMap_represents cC inp hDL s t g)
  refine ⟨homotopyMatrix c nativeH, ?_⟩
  rw [AlgorithmTwoLinearComparison.contractionInput_correct,prepareCone_correct]
  exact ⟨homotopyMatrix_equation c _ hd nativeH,homotopyMatrix_homogeneous c nativeH⟩

end

structure StoredHomotopy (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
    (g : StoredGamma cC inp hDL s t) where
  matrix : LaurentArithmetic.DenseMatrix K D (coneRank cC inp hDL s) (coneRank cC inp hDL s) (homotopyRadius cC inp hDL s)
  equation : coneMatrix (LaurentArithmetic.matrixDenote t.differential)
      (LaurentArithmetic.matrixDenote inp.differential) (LaurentArithmetic.matrixDenote g.matrix) * LaurentArithmetic.matrixDenote matrix +
    LaurentArithmetic.matrixDenote matrix * coneMatrix (LaurentArithmetic.matrixDenote t.differential)
      (LaurentArithmetic.matrixDenote inp.differential) (LaurentArithmetic.matrixDenote g.matrix) = 1
  homogeneous : Homogeneous
    (coneDegree (AlgorithmTwoToricData.degrees D s.multiplicities) (totalDegree cC.rank (-(L:ℤ)) (inputLength L)))
    (coneDegree (AlgorithmTwoToricData.degrees D s.multiplicities) (totalDegree cC.rank (-(L:ℤ)) (inputLength L))) (-1)
    (LaurentArithmetic.matrixDenote matrix)

def homotopyProgram (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
    (g : StoredGamma cC inp hDL s t) : Work K (StoredHomotopy cC inp hDL s t g) :=
  let preparation := prepareCone cC inp hDL s t g
  let system := AlgorithmTwoLinearComparison.contractionInput preparation.value
    (coneDegree (AlgorithmTwoToricData.degrees D s.multiplicities) (totalDegree cC.rank (-(L:ℤ)) (inputLength L)))
  let solved := AlgorithmTwoLinearComparison.solveOfExists system (cone_solvable cC inp hDL s t g)
  have hc := (AlgorithmTwoLinearComparison.contractionInput_correct _ _ _).mp
    (AlgorithmTwoLinearComparison.solveOfExists_correct system (cone_solvable cC inp hDL s t g))
  have heq : _ := by rw [prepareCone_correct cC inp hDL s t g] at hc; exact hc.1
  { value := ⟨solved.value,heq,hc.2⟩, trace := preparation.trace ++ solved.trace }

theorem homotopyProgram_cost (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
    (g : StoredGamma cC inp hDL s t) :
    (homotopyProgram cC inp hDL s t g).cost ≤
      (AlgorithmTwoToricData.totalRank D s.multiplicities)^2 * LaurentArithmetic.boxSize D (coneRadius cC inp hDL s) +
      AlgorithmTwoLinearComparison.costBound D (coneRank cC inp hDL s) (coneRank cC inp hDL s) 0 (coneRadius cC inp hDL s) := by
  simp only [homotopyProgram,Work.cost,List.length_append]
  apply Nat.add_le_add
  · simpa only [prepareCone,pow_two,Work.cost] using
      (AlgorithmTwoLinearComparison.coneArrayProgram_cost
        (LaurentArithmetic.matrixPad t.differential (coneRadius cC inp hDL s))
        (LaurentArithmetic.matrixPad inp.differential (coneRadius cC inp hDL s))
        (LaurentArithmetic.matrixPad g.matrix (coneRadius cC inp hDL s))).le
  · exact AlgorithmTwoLinearComparison.solveOfExists_cost _ _

structure StoredExtraction (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
    (g : StoredGamma cC inp hDL s t) (H : StoredHomotopy cC inp hDL s t g) where
  arrays : AlgorithmTwoLinearComparison.Extracted K D (AlgorithmTwoToricData.totalRank D s.multiplicities)
    (inputRank cC L) (homotopyRadius cC inp hDL s)
  correct : arrays = (AlgorithmTwoLinearComparison.extractProgram H.matrix).value

def extractionProgram (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
    (g : StoredGamma cC inp hDL s t) (H : StoredHomotopy cC inp hDL s t g) : Work K (StoredExtraction cC inp hDL s t g H) :=
  let run := AlgorithmTwoLinearComparison.extractProgram H.matrix
  { value := ⟨run.value,rfl⟩, trace := run.trace }

theorem extractionProgram_cost (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
    (g : StoredGamma cC inp hDL s t) (H : StoredHomotopy cC inp hDL s t g) :
    (extractionProgram cC inp hDL s t g H).cost = (inputRank cC L)^2 * LaurentArithmetic.boxSize D (homotopyRadius cC inp hDL s) := by
  simpa only [extractionProgram,Work.cost,pow_two] using AlgorithmTwoLinearComparison.extractProgram_cost H.matrix

noncomputable section

def computedEquivalence (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
    (g : StoredGamma cC inp hDL s t) (H : StoredHomotopy cC inp hDL s t g) :
    HomotopyEquiv (AlgorithmTwoToricData.nativeStack D s.multiplicities K) C :=
  blockHomotopyEquiv (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K) (inputCoordinates (L := L) cC)
    _ _ (storedTarget_represents cC inp hDL s t) inp.represents (gammaMap cC inp hDL s t g)
    (LaurentArithmetic.matrixDenote g.matrix) (gammaMap_represents cC inp hDL s t g)
    (LaurentArithmetic.matrixDenote H.matrix) H.homogeneous H.equation

end
end Decoupling.HighDim.AlgorithmTwoPipeline
