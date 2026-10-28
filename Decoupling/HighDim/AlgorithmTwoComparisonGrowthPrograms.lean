import Decoupling.HighDim.AlgorithmTwoComparisonGrowth

/-! # Polynomial bounds attached to executed comparison/cone programs
The semantic existence inputs certify solvability only. The costs and
output dimensions below are derived from the recorded program traces.
-/
namespace Decoupling.HighDim.AlgorithmTwoComparisonGrowth
open CategoryTheory HomologicalComplex Matrix ArithmeticCost AlgorithmTwoLinearComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D n m k h s : ℕ}

theorem solve_cost_polynomial (v : Input K D n m k h)
    (hn : n ≤ s) (hm : m ≤ s) (hk : k ≤ s) (hh : h ≤ s) :
    (solve v).cost ≤ (polynomial D).eval s := by
  rw [polynomial_eval]
  exact (solve_cost v).trans ((Nat.le_add_left _ _).trans (comparisonCost_le hn hm hk hh))

theorem solveOfExists_cost_polynomial (v : Input K D n m k h) (hex : ∃ X, v.Satisfied X)
    (hn : n ≤ s) (hm : m ≤ s) (hk : k ≤ s) (hh : h ≤ s) :
    (solveOfExists v hex).cost ≤ (polynomial D).eval s := by
  rw [polynomial_eval]
  exact (solveOfExists_cost v hex).trans ((Nat.le_add_left _ _).trans (comparisonCost_le hn hm hk hh))

variable {T C : CochainComplex (ModuleCat (Laurent K D)) ℤ}

theorem comparisonProgram_cost_polynomial (t : Represented T m h) (c : Represented C n h)
    (p : Prescribed t.coordinates c.coordinates k h) (hex : ∃ f : T ⟶ C, p.Realized f)
    (hn : n ≤ s) (hm : m ≤ s) (hk : k ≤ s) (hh : h ≤ s) :
    (comparisonProgram t c p hex).cost ≤ (polynomial D).eval s := by
  rw [polynomial_eval]
  exact (comparisonProgram_cost t c p hex).trans (comparisonCost_le hn hm hk hh)

variable (f : T ⟶ C) [QuasiIso f] (t : Represented T m h) (c : Represented C n h)
  (originalT : StableFree.Coordinates T) (originalC : StableFree.Coordinates C)
  (upperT upperC : ℤ) [T.IsStrictlyLE upperT] [C.IsStrictlyLE upperC]
  (A : LaurentArithmetic.DenseMatrix K D n m h)
  (hA : ∀ j x, LaurentArithmetic.matrixDenote A *ᵥ t.coordinates.embed j x =
      c.coordinates.embed j ((f.f j).hom x))

theorem coneSolveProgram_cost_polynomial (hm : m ≤ s) (hn : n ≤ s) (hh : h ≤ s) :
    (coneSolveProgram f t c originalT originalC upperT upperC A hA).cost ≤ (polynomial D).eval s := by
  rw [polynomial_eval]
  exact (coneSolveProgram_cost f t c originalT originalC upperT upperC A hA).trans
    ((Nat.le_add_right _ _).trans (coneCost_le hm hn hh))

theorem coneSolveExtractProgram_cost_polynomial (hm : m ≤ s) (hn : n ≤ s) (hh : h ≤ s) :
    (coneSolveExtractProgram f t c originalT originalC upperT upperC A hA).cost ≤ (polynomial D).eval s := by
  rw [polynomial_eval]
  exact (coneSolveExtractProgram_cost f t c originalT originalC upperT upperC A hA).trans
    (coneCost_le hm hn hh)

end Decoupling.HighDim.AlgorithmTwoComparisonGrowth
