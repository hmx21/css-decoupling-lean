import Decoupling.HighDim.SequentialPipelineConeSemantics
import Decoupling.HighDim.SequentialContractionProgram

/-!
# HD016: descending contraction of the actual comparison cone

Source: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of
Algorithm 2”. The old global solve stays in AlgorithmTwoPipelineCone.
The new output radius is the proved recursive radius of all degree solves.
The following extraction and native equivalence use precisely this output.
-/
namespace Decoupling.HighDim.SequentialPipeline
open CategoryTheory HomologicalComplex Matrix ArithmeticCost AlgorithmTwoFiniteComplex
open AlgorithmTwoPipeline
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
variable (inp : Input (D := D) (L := L) (h := h) cC) (hDL : D ≤ L)

abbrev contractionSteps (L : ℕ) := 2*(L+1)+1

abbrev homotopyRadius (s : InputLayers cC inp hDL) :=
  SequentialContractionGrowth.outputRadius D (coneRank cC inp hDL s)
    (coneRadius cC inp hDL s) (contractionSteps L)

def c4Radius (s : InputLayers cC inp hDL) : ℕ :=
  max (coneRadius cC inp hDL s) (homotopyRadius cC inp hDL s)

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

/-- Each degree is solved once, from L+1 down to -L-1. The extra zero
endpoint degrees make the uniform interval independent of input ranks. -/
def homotopyProgram (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
    (g : StoredGamma cC inp hDL s t) : Work K (StoredHomotopy cC inp hDL s t g) :=
  let preparation := prepareCone cC inp hDL s t g
  let degree := coneDegree (AlgorithmTwoToricData.degrees D s.multiplicities)
    (totalDegree cC.rank (-(L:ℤ)) (inputLength L))
  have htop : ∀ j, degree.get j ≤ (L:ℤ)+1 := fun j =>
    (cone_degree_bounds cC inp hDL s j).2
  have hbottom : ∀ j, (L:ℤ)+1-(contractionSteps L:ℤ) < degree.get j := by
    intro j
    have hb := (cone_degree_bounds cC inp hDL s j).1
    dsimp only [contractionSteps]
    push_cast
    dsimp only [degree] at *
    omega
  have hd := cone_differential_properties cC inp hDL s t g
  have hex := SequentialContraction.exact_of_contraction _
    (cone_contractible cC inp hDL s t g)
  let solved := SequentialContraction.program degree preparation.value ((L:ℤ)+1)
    (contractionSteps L) htop hbottom hd.1 hd.2 hex
  have heq : _ := solved.value.equation
  have he : _ := by rw [prepareCone_correct cC inp hDL s t g] at heq; exact heq
  { value := ⟨solved.value.matrix,he,solved.value.homogeneous⟩,
    trace := preparation.trace ++ solved.trace }

theorem homotopyProgram_cost (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
    (g : StoredGamma cC inp hDL s t) :
    (homotopyProgram cC inp hDL s t g).cost ≤
      (AlgorithmTwoToricData.totalRank D s.multiplicities)^2 *
        LaurentArithmetic.boxSize D (coneRadius cC inp hDL s) +
      SequentialContractionGrowth.totalCost D (coneRank cC inp hDL s)
        (coneRadius cC inp hDL s) (contractionSteps L) := by
  simp only [homotopyProgram,Work.cost,List.length_append]
  apply Nat.add_le_add
  · simpa only [prepareCone,pow_two,Work.cost] using
      (AlgorithmTwoLinearComparison.coneArrayProgram_cost
        (LaurentArithmetic.matrixPad t.differential (coneRadius cC inp hDL s))
        (LaurentArithmetic.matrixPad inp.differential (coneRadius cC inp hDL s))
        (LaurentArithmetic.matrixPad g.matrix (coneRadius cC inp hDL s))).le
  · exact SequentialContraction.program_cost _ _ _ _ _ _ _ _ _

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
end Decoupling.HighDim.SequentialPipeline
