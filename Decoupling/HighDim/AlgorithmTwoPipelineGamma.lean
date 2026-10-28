import Decoupling.HighDim.AlgorithmTwoPipelineFormal
import Decoupling.HighDim.AlgorithmTwoToricDataSupport
import Decoupling.HighDim.AlgorithmTwoLinearComparisonGraded

/-!
# The actual prescribed comparison solve using shared stored target data

Native maps occur only in semantic proofs. The executable stage consumes
materialized arrays and integer degree labels, records the sign preparation
and solver traces, and stores the matrix which it actually computed.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipeline
open CategoryTheory Matrix ArithmeticCost AlgorithmTwoFiniteComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
variable (inp : Input (D := D) (L := L) (h := h) cC) (hDL : D ≤ L)

structure StoredTarget (s : InputLayers cC inp hDL) where
  differential : LaurentArithmetic.DenseMatrix K D (AlgorithmTwoToricData.totalRank D s.multiplicities)
    (AlgorithmTwoToricData.totalRank D s.multiplicities) 1
  top : LaurentArithmetic.DenseMatrix K D (AlgorithmTwoToricData.totalRank D s.multiplicities)
    (AlgorithmTwoToricData.copyCount D s.multiplicities) 0
  correct : (differential,top) = (AlgorithmTwoToricData.targetProgram (K := K) D s.multiplicities).value

def storeTargetProgram (s : InputLayers cC inp hDL) : Work K (StoredTarget cC inp hDL s) :=
  let run := AlgorithmTwoToricData.targetProgram (K := K) D s.multiplicities
  { value := ⟨run.value.1,run.value.2,Prod.mk.eta⟩, trace := run.trace }

@[simp] theorem storeTargetProgram_cost (s : InputLayers cC inp hDL) :
    (storeTargetProgram cC inp hDL s).cost = 1 := AlgorithmTwoToricData.targetProgram_cost D s.multiplicities

def prepareComparison (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s) :
    Work K (AlgorithmTwoLinearComparison.Input K D (inputRank cC L)
      (AlgorithmTwoToricData.totalRank D s.multiplicities) (AlgorithmTwoToricData.copyCount D s.multiplicities)
      s.commonRadius) :=
  AlgorithmTwoLinearComparison.comparisonInput (LaurentArithmetic.matrixPad t.differential s.commonRadius)
    (LaurentArithmetic.matrixPad inp.differential s.commonRadius)
    (LaurentArithmetic.matrixPad t.top s.commonRadius) (targetCocycles cC inp hDL s)
    (AlgorithmTwoToricData.degrees D s.multiplicities) (totalDegree cC.rank (-(L:ℤ)) (inputLength L))

noncomputable section

theorem storedTarget_represents (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s) :
    (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K).RepresentsDifferential
      (LaurentArithmetic.matrixDenote t.differential) := by
  have he := congrArg Prod.fst t.correct
  dsimp only [Prod.fst] at he
  rw [he]
  exact (AlgorithmTwoToricData.targetProgram_spec D s.multiplicities K).1

theorem storedTarget_top (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
    (a : Fin (AlgorithmTwoToricData.copyCount D s.multiplicities)) :
    (LaurentArithmetic.matrixDenote t.top).col a =
      (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K).embed
        (((AlgorithmTwoToricData.copyEquiv D s.multiplicities a).1.val:ℤ)+1)
        (AlgorithmTwoComparison.stackTop K D
          (Toric.copyForms D (AlgorithmTwoToricData.multiplicities D s.multiplicities))
          (AlgorithmTwoToricData.copyEquiv D s.multiplicities a)) := by
  have he := congrArg Prod.snd t.correct
  dsimp only [Prod.snd] at he
  erw [he]
  exact (AlgorithmTwoToricData.targetProgram_spec D s.multiplicities K).2.2.1 a

theorem prepareComparison_correct (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
    (A : Matrix (Fin (inputRank cC L)) (Fin (AlgorithmTwoToricData.totalRank D s.multiplicities)) (Laurent K D)) :
    (prepareComparison cC inp hDL s t).value.Satisfied A ↔
      LaurentArithmetic.matrixDenote inp.differential * A = A * LaurentArithmetic.matrixDenote t.differential ∧
      A * LaurentArithmetic.matrixDenote t.top = LaurentArithmetic.matrixDenote (targetCocycles cC inp hDL s) ∧
      Homogeneous (AlgorithmTwoToricData.degrees D s.multiplicities)
        (totalDegree cC.rank (-(L:ℤ)) (inputLength L)) 0 A := by
  rw [prepareComparison, AlgorithmTwoLinearComparison.comparisonInput_correct]
  rw [LaurentArithmetic.matrixPad_correct _ s.input_le_commonRadius,
    LaurentArithmetic.matrixPad_correct _ s.one_le_commonRadius,
    LaurentArithmetic.matrixPad_correct _ (Nat.zero_le _)]

theorem prepareComparison_solvable (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s) :
    ∃ A, (prepareComparison cC inp hDL s t).value.Satisfied A := by
  obtain ⟨f,hf,htop⟩ := stored_comparison_exists cC inp hDL s
  let ft := AlgorithmTwoToricData.totalCoordinates D s.multiplicities K
  let fc := inputCoordinates (L := L) cC
  refine ⟨cochainMatrix ft fc f, (prepareComparison_correct cC inp hDL s t _).mpr ⟨?_,?_,?_⟩⟩
  · exact cochainMatrix_comm ft fc _ _ (storedTarget_represents cC inp hDL s t) inp.represents f
  · funext i a
    change (cochainMatrix ft fc f *ᵥ (LaurentArithmetic.matrixDenote t.top).col a) i = _
    rw [storedTarget_top,cochainMatrix_mulVec,htop]
    exact congrFun (targetCocycles_native cC inp hDL s a).symm i
  · exact cochainMatrix_homogeneous ft fc f

end

abbrev gammaRadius (s : InputLayers cC inp hDL) :=
  AlgorithmTwoLinearComparison.resultBox D (inputRank cC L) (AlgorithmTwoToricData.totalRank D s.multiplicities)
    (AlgorithmTwoToricData.copyCount D s.multiplicities) s.commonRadius

structure StoredGamma (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s) where
  matrix : LaurentArithmetic.DenseMatrix K D (inputRank cC L)
    (AlgorithmTwoToricData.totalRank D s.multiplicities) (gammaRadius cC inp hDL s)
  correct : (prepareComparison cC inp hDL s t).value.Satisfied (LaurentArithmetic.matrixDenote matrix)

def gammaProgram (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s) :
    Work K (StoredGamma cC inp hDL s t) :=
  let preparation := prepareComparison cC inp hDL s t
  let solved := AlgorithmTwoLinearComparison.solveOfExists preparation.value (prepareComparison_solvable cC inp hDL s t)
  { value := ⟨solved.value,AlgorithmTwoLinearComparison.solveOfExists_correct _ _⟩
    trace := preparation.trace ++ solved.trace }

theorem gammaProgram_cost (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s) :
    (gammaProgram cC inp hDL s t).cost ≤
      (AlgorithmTwoToricData.totalRank D s.multiplicities)^2 * LaurentArithmetic.boxSize D s.commonRadius +
      AlgorithmTwoLinearComparison.costBound D (inputRank cC L)
        (AlgorithmTwoToricData.totalRank D s.multiplicities) (AlgorithmTwoToricData.copyCount D s.multiplicities) s.commonRadius := by
  simp only [gammaProgram, Work.cost,List.length_append]
  have hp := AlgorithmTwoLinearComparison.comparisonInput_cost
    (LaurentArithmetic.matrixPad t.differential s.commonRadius)
    (LaurentArithmetic.matrixPad inp.differential s.commonRadius)
    (LaurentArithmetic.matrixPad t.top s.commonRadius) (targetCocycles cC inp hDL s)
    (AlgorithmTwoToricData.degrees D s.multiplicities) (totalDegree cC.rank (-(L:ℤ)) (inputLength L))
  apply Nat.add_le_add
  · simpa only [prepareComparison,pow_two,Work.cost] using hp.le
  · exact AlgorithmTwoLinearComparison.solveOfExists_cost _ _

noncomputable section

def gammaMap (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s) (g : StoredGamma cC inp hDL s t) :
    AlgorithmTwoToricData.nativeStack D s.multiplicities K ⟶ C :=
  cochainMap (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K) (inputCoordinates (L := L) cC)
    _ _ (storedTarget_represents cC inp hDL s t) inp.represents (LaurentArithmetic.matrixDenote g.matrix)
    ((prepareComparison_correct cC inp hDL s t _).mp g.correct).2.2
    ((prepareComparison_correct cC inp hDL s t _).mp g.correct).1

theorem gammaMap_represents (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
    (g : StoredGamma cC inp hDL s t) (j : ℤ) (x : (AlgorithmTwoToricData.nativeStack D s.multiplicities K).X j) :
    LaurentArithmetic.matrixDenote g.matrix *ᵥ (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K).embed j x =
      (inputCoordinates (L := L) cC).embed j (((gammaMap cC inp hDL s t g).f j).hom x) :=
  (component_embed_zero (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K)
    (inputCoordinates (L := L) cC) (LaurentArithmetic.matrixDenote g.matrix) j
    ((prepareComparison_correct cC inp hDL s t _).mp g.correct).2.2 x).symm

theorem gammaMap_top (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
    (g : StoredGamma cC inp hDL s t) (a : Fin (AlgorithmTwoToricData.copyCount D s.multiplicities)) :
    (gammaMap cC inp hDL s t g).f (((AlgorithmTwoToricData.copyEquiv D s.multiplicities a).1.val:ℤ)+1)
      (AlgorithmTwoComparison.stackTop K D
        (Toric.copyForms D (AlgorithmTwoToricData.multiplicities D s.multiplicities))
          (AlgorithmTwoToricData.copyEquiv D s.multiplicities a)) =
      nativeStoredCycle cC inp hDL s (AlgorithmTwoToricData.copyEquiv D s.multiplicities a) := by
  apply (inputCoordinates (L := L) cC).embed_injective
  rw [← gammaMap_represents, ← storedTarget_top]
  have he := congrArg (fun A => A.col a) ((prepareComparison_correct cC inp hDL s t _).mp g.correct).2.1
  exact he.trans (targetCocycles_native cC inp hDL s a)

theorem gammaMap_quasiIso (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
    (g : StoredGamma cC inp hDL s t) : QuasiIso (gammaMap cC inp hDL s t g) := by
  apply stored_solution_quasiIso cC inp hDL s
  intro i
  obtain ⟨a,rfl⟩ := (AlgorithmTwoToricData.copyEquiv D s.multiplicities).surjective i
  exact gammaMap_top cC inp hDL s t g a

end
end Decoupling.HighDim.AlgorithmTwoPipeline
