import Decoupling.HighDim.AlgorithmTwoLinearComparisonConeNative
import Decoupling.HighDim.AlgorithmTwoLinearComparisonExtract
import Decoupling.HighDim.AlgorithmTwoFiniteComplexBlockEquivalence

/-! # Actual solved cone outputs, inverse arrays, and the same native equivalence -/
namespace Decoupling.HighDim.AlgorithmTwoLinearComparison
open CategoryTheory HomologicalComplex Matrix ArithmeticCost AlgorithmTwoFiniteComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D m n h : ℕ}
variable {T C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
variable (f : T ⟶ C) [QuasiIso f] (t : Represented T m h) (c : Represented C n h)
  (originalT : StableFree.Coordinates T) (originalC : StableFree.Coordinates C)
  (upperT upperC : ℤ) [T.IsStrictlyLE upperT] [C.IsStrictlyLE upperC]
  (A : LaurentArithmetic.DenseMatrix K D n m h)
  (hA : ∀ j x, LaurentArithmetic.matrixDenote A *ᵥ t.coordinates.embed j x =
      c.coordinates.embed j ((f.f j).hom x))

theorem coneSolveProgram_correct :
    let H := LaurentArithmetic.matrixDenote (coneSolveProgram f t c originalT originalC upperT upperC A hA).value
    coneMatrix (LaurentArithmetic.matrixDenote t.differential) (LaurentArithmetic.matrixDenote c.differential)
        (LaurentArithmetic.matrixDenote A) * H +
      H * coneMatrix (LaurentArithmetic.matrixDenote t.differential) (LaurentArithmetic.matrixDenote c.differential)
        (LaurentArithmetic.matrixDenote A) = 1 ∧
    Homogeneous (coneDegree t.coordinates.degree c.coordinates.degree)
      (coneDegree t.coordinates.degree c.coordinates.degree) (-1) H := by
  have he := contractionProgram_correct (coneRepresentation f t c A hA)
    ⟨AlgorithmTwoComparison.coneContraction f originalT originalC upperT upperC⟩
  change LaurentArithmetic.matrixDenote (coneArrayProgram t.differential c.differential A).value *
      LaurentArithmetic.matrixDenote (coneSolveProgram f t c originalT originalC upperT upperC A hA).value +
    LaurentArithmetic.matrixDenote (coneSolveProgram f t c originalT originalC upperT upperC A hA).value *
      LaurentArithmetic.matrixDenote (coneArrayProgram t.differential c.differential A).value = 1 ∧ _ at he
  rw [coneArrayProgram_correct] at he
  exact he

def coneSolveExtractProgram : Work K (Extracted K D m n (resultBox D (m+n) (m+n) 0 h)) :=
  Work.bind (coneSolveProgram f t c originalT originalC upperT upperC A hA) extractProgram

theorem coneSolveExtractProgram_cost :
    (coneSolveExtractProgram f t c originalT originalC upperT upperC A hA).cost ≤
      m*m*LaurentArithmetic.boxSize D h + costBound D (m+n) (m+n) 0 h +
        n*n*LaurentArithmetic.boxSize D (resultBox D (m+n) (m+n) 0 h) := by
  rw [coneSolveExtractProgram, Work.bind_cost, extractProgram_cost]
  exact Nat.add_le_add_right (coneSolveProgram_cost f t c originalT originalC upperT upperC A hA) _

noncomputable def coneSolvedEquivalence : HomotopyEquiv T C :=
  blockHomotopyEquiv t.coordinates c.coordinates _ _ t.represents c.represents f
    (LaurentArithmetic.matrixDenote A) hA
    (LaurentArithmetic.matrixDenote (coneSolveProgram f t c originalT originalC upperT upperC A hA).value)
    (coneSolveProgram_correct f t c originalT originalC upperT upperC A hA).2
    (coneSolveProgram_correct f t c originalT originalC upperT upperC A hA).1

@[simp] theorem coneSolvedEquivalence_hom :
    (coneSolvedEquivalence f t c originalT originalC upperT upperC A hA).hom = f := rfl

theorem coneSolvedEquivalence_inverse (j : ℤ) (x : C.X j) :
    LaurentArithmetic.matrixDenote (coneSolveExtractProgram f t c originalT originalC upperT upperC A hA).value.inverse *ᵥ
      c.coordinates.embed j x = t.coordinates.embed j
      ((((coneSolvedEquivalence f t c originalT originalC upperT upperC A hA).inv).f j).hom x) := by
  rw [coneSolveExtractProgram, Work.bind_value, extractProgram_inverse]
  exact blockHomotopyEquiv_inv_represents _ _ _ _ _ _ _ _ _ _ _ _ j x

theorem coneSolvedEquivalence_source (a b : ℤ) (hab : b+1=a) (x : T.X a) :
    LaurentArithmetic.matrixDenote (coneSolveExtractProgram f t c originalT originalC upperT upperC A hA).value.sourceHomotopy *ᵥ
      t.coordinates.embed a x = t.coordinates.embed b
      ((((coneSolvedEquivalence f t c originalT originalC upperT upperC A hA).homotopyHomInvId).hom a b).hom x) := by
  rw [coneSolveExtractProgram, Work.bind_value, extractProgram_source]
  exact blockHomotopyEquiv_source_represents _ _ _ _ _ _ _ _ _ _ _ _ a b hab x

theorem coneSolvedEquivalence_target (a b : ℤ) (hab : b+1=a) (x : C.X a) :
    LaurentArithmetic.matrixDenote (coneSolveExtractProgram f t c originalT originalC upperT upperC A hA).value.targetHomotopy *ᵥ
      c.coordinates.embed a x = c.coordinates.embed b
      ((((coneSolvedEquivalence f t c originalT originalC upperT upperC A hA).homotopyInvHomId).hom a b).hom x) := by
  rw [coneSolveExtractProgram, Work.bind_value, extractProgram_target]
  exact blockHomotopyEquiv_target_represents _ _ _ _ _ _ _ _ _ _ _ _ a b hab x

end Decoupling.HighDim.AlgorithmTwoLinearComparison
