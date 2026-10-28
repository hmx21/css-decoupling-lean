import Decoupling.HighDim.AlgorithmTwoInvertibleLinear
import Decoupling.HighDim.AlgorithmTwoInvertibleSolvability
import Decoupling.HighDim.AlgorithmTwoInvertibleRightSides

/-! # The four actual known-solvable lift calls and their combined trace -/
namespace Decoupling.HighDim.AlgorithmTwoInvertible
open Matrix ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {K : Type*} [Field K] [DecidableEq K] {D c0 c1 t0 t1 h : ℕ}

noncomputable def FourSolvable (dC : Matrix (Fin c1) (Fin c0) (Laurent K D))
    (dT : Matrix (Fin t1) (Fin t0) (Laurent K D))
    (F : Matrix (Fin c1) (Fin t1) (Laurent K D)) (G : Matrix (Fin t1) (Fin c1) (Laurent K D)) : Prop :=
  (∃ X, dC*X=F*dT) ∧ (∃ X, dT*X=G*dC) ∧ (∃ X, dC*X=1-F*G) ∧ (∃ X, dT*X=1-G*F)

structure FourSolutions (K : Type*) (D c0 c1 t0 t1 h : ℕ) where
  phi0 : LaurentArithmetic.DenseMatrix K D c0 t0 (outputBox D c1 t0 (h+h))
  psi0 : LaurentArithmetic.DenseMatrix K D t0 c0 (outputBox D t1 c0 (h+h))
  etaC : LaurentArithmetic.DenseMatrix K D c0 c1 (outputBox D c1 c1 (h+h))
  etaT : LaurentArithmetic.DenseMatrix K D t0 t1 (outputBox D t1 t1 (h+h))

variable (dC : LaurentArithmetic.DenseMatrix K D c1 c0 h)
  (dT : LaurentArithmetic.DenseMatrix K D t1 t0 h)
  (F : LaurentArithmetic.DenseMatrix K D c1 t1 h) (G : LaurentArithmetic.DenseMatrix K D t1 c1 h)
  (hs : FourSolvable (LaurentArithmetic.matrixDenote dC) (LaurentArithmetic.matrixDenote dT)
    (LaurentArithmetic.matrixDenote F) (LaurentArithmetic.matrixDenote G))

include hs in
omit [DecidableEq K] in
private theorem forward_solvable : ∃ X,
    LaurentArithmetic.matrixDenote (LaurentArithmetic.matrixPad dC (h+h)) * X =
      LaurentArithmetic.matrixDenote (rightSidesProgram dC dT F G).value.forward := by
  rw [LaurentArithmetic.matrixPad_correct _ (by omega), (rightSidesProgram_correct dC dT F G).1]
  exact hs.1

include hs in
omit [DecidableEq K] in
private theorem backward_solvable : ∃ X,
    LaurentArithmetic.matrixDenote (LaurentArithmetic.matrixPad dT (h+h)) * X =
      LaurentArithmetic.matrixDenote (rightSidesProgram dC dT F G).value.backward := by
  rw [LaurentArithmetic.matrixPad_correct _ (by omega), (rightSidesProgram_correct dC dT F G).2.1]
  exact hs.2.1

include hs in
omit [DecidableEq K] in
private theorem errorC_solvable : ∃ X,
    LaurentArithmetic.matrixDenote (LaurentArithmetic.matrixPad dC (h+h)) * X =
      LaurentArithmetic.matrixDenote (rightSidesProgram dC dT F G).value.errorC := by
  rw [LaurentArithmetic.matrixPad_correct _ (by omega), (rightSidesProgram_correct dC dT F G).2.2.1]
  exact hs.2.2.1

include hs in
omit [DecidableEq K] in
private theorem errorT_solvable : ∃ X,
    LaurentArithmetic.matrixDenote (LaurentArithmetic.matrixPad dT (h+h)) * X =
      LaurentArithmetic.matrixDenote (rightSidesProgram dC dT F G).value.errorT := by
  rw [LaurentArithmetic.matrixPad_correct _ (by omega), (rightSidesProgram_correct dC dT F G).2.2.2]
  exact hs.2.2.2

/-- Each right side and each solution is materialized once. All four
solver traces are retained together with the actual right-side arithmetic. -/
def fourProgram : Work K (FourSolutions K D c0 c1 t0 t1 h) :=
  let rhs := rightSidesProgram dC dT F G
  let c := LaurentArithmetic.matrixPad dC (h+h)
  let t := LaurentArithmetic.matrixPad dT (h+h)
  let forward := solveOfExists c rhs.value.forward (forward_solvable dC dT F G hs)
  let backward := solveOfExists t rhs.value.backward (backward_solvable dC dT F G hs)
  let errorC := solveOfExists c rhs.value.errorC (errorC_solvable dC dT F G hs)
  let errorT := solveOfExists t rhs.value.errorT (errorT_solvable dC dT F G hs)
  { value := ⟨forward.value, backward.value, errorC.value, errorT.value⟩
    trace := rhs.trace ++ forward.trace ++ backward.trace ++ errorC.trace ++ errorT.trace }

theorem fourProgram_correct :
    let s := (fourProgram dC dT F G hs).value
    LaurentArithmetic.matrixDenote dC * LaurentArithmetic.matrixDenote s.phi0 =
        LaurentArithmetic.matrixDenote F * LaurentArithmetic.matrixDenote dT ∧
    LaurentArithmetic.matrixDenote dT * LaurentArithmetic.matrixDenote s.psi0 =
        LaurentArithmetic.matrixDenote G * LaurentArithmetic.matrixDenote dC ∧
    LaurentArithmetic.matrixDenote dC * LaurentArithmetic.matrixDenote s.etaC =
        1-LaurentArithmetic.matrixDenote F*LaurentArithmetic.matrixDenote G ∧
    LaurentArithmetic.matrixDenote dT * LaurentArithmetic.matrixDenote s.etaT =
        1-LaurentArithmetic.matrixDenote G*LaurentArithmetic.matrixDenote F := by
  have hf := solveOfExists_correct _ _ (forward_solvable dC dT F G hs)
  have hb := solveOfExists_correct _ _ (backward_solvable dC dT F G hs)
  have hc := solveOfExists_correct _ _ (errorC_solvable dC dT F G hs)
  have ht := solveOfExists_correct _ _ (errorT_solvable dC dT F G hs)
  rw [LaurentArithmetic.matrixPad_correct _ (by omega), (rightSidesProgram_correct dC dT F G).1] at hf
  rw [LaurentArithmetic.matrixPad_correct _ (by omega), (rightSidesProgram_correct dC dT F G).2.1] at hb
  rw [LaurentArithmetic.matrixPad_correct _ (by omega), (rightSidesProgram_correct dC dT F G).2.2.1] at hc
  rw [LaurentArithmetic.matrixPad_correct _ (by omega), (rightSidesProgram_correct dC dT F G).2.2.2] at ht
  exact ⟨hf,hb,hc,ht⟩

def fourCost (D c0 c1 t0 t1 h : ℕ) : ℕ :=
  rightSidesCost D c0 c1 t0 t1 h +
    LaurentLinearSolver.solveCost D (c1*t0) (c0*t0) (h+h) +
    LaurentLinearSolver.solveCost D (t1*c0) (t0*c0) (h+h) +
    LaurentLinearSolver.solveCost D (c1*c1) (c0*c1) (h+h) +
    LaurentLinearSolver.solveCost D (t1*t1) (t0*t1) (h+h)

theorem fourProgram_cost : (fourProgram dC dT F G hs).cost ≤ fourCost D c0 c1 t0 t1 h := by
  simp only [fourProgram, Work.cost, List.length_append, fourCost]
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add (rightSidesProgram_cost dC dT F G).le
          (solveOfExists_cost _ _ (forward_solvable dC dT F G hs)))
        (solveOfExists_cost _ _ (backward_solvable dC dT F G hs)))
      (solveOfExists_cost _ _ (errorC_solvable dC dT F G hs)))
    (solveOfExists_cost _ _ (errorT_solvable dC dT F G hs))

/-- Actual comparison data are built from the four executed outputs. -/
noncomputable def comparisonData : Stabilization.ComparisonData (Laurent K D) (Fin c0) (Fin c1) (Fin t0) (Fin t1) where
  dC := LaurentArithmetic.matrixDenote dC
  dT := LaurentArithmetic.matrixDenote dT
  phi1 := LaurentArithmetic.matrixDenote F
  psi1 := LaurentArithmetic.matrixDenote G
  phi0 := LaurentArithmetic.matrixDenote (fourProgram dC dT F G hs).value.phi0
  psi0 := LaurentArithmetic.matrixDenote (fourProgram dC dT F G hs).value.psi0
  etaC := LaurentArithmetic.matrixDenote (fourProgram dC dT F G hs).value.etaC
  etaT := LaurentArithmetic.matrixDenote (fourProgram dC dT F G hs).value.etaT
  forward := (fourProgram_correct dC dT F G hs).1
  backward := (fourProgram_correct dC dT F G hs).2.1
  homotopyC := (fourProgram_correct dC dT F G hs).2.2.1
  homotopyT := (fourProgram_correct dC dT F G hs).2.2.2

end Decoupling.HighDim.AlgorithmTwoInvertible
