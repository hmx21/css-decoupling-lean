import Decoupling.HighDim.AlgorithmTwoCohomologyGrowth
import Decoupling.HighDim.AlgorithmTwoPipelineRadius
import Decoupling.HighDim.PaperInputSize

/-!
# HD012 all computed layers and the next-stage resource budget

Only D−1 actual cohomology computations occur. Their stored output
dimensions and radii bound the explicit toric target, prescribed columns,
and common radius used by the comparison solve.
-/
namespace Decoupling.HighDim.AlgorithmTwoLayersGrowth
open ArithmeticGrowth AlgorithmTwoPipeline
open AlgorithmTwoCohomologyGrowth

def bound (D s : ℕ) :=
  s+1+(D+1)*(2^D+3)*AlgorithmTwoCohomologyGrowth.bound D s

def expression (D : ℕ) : Expression :=
  .add (.add .input (.constant 1))
    (.mul (.constant ((D+1)*(2^D+3))) (AlgorithmTwoCohomologyGrowth.expression D))

theorem expression_eval (D s : ℕ) : (expression D).eval s = bound D s := by
  simp only [expression, Expression.eval, AlgorithmTwoCohomologyGrowth.expression_eval, bound]

noncomputable def polynomial (D : ℕ) : Polynomial ℕ := (expression D).polynomial

theorem polynomial_eval (D s : ℕ) : (polynomial D).eval s = bound D s :=
  (Expression.polynomial_eval _ _).trans (expression_eval D s)

theorem bound_monotone (D : ℕ) : Monotone (bound D) := by
  intro s t h
  rw [← expression_eval, ← expression_eval]
  exact (expression D).monotone h

theorem input_le_bound (D s : ℕ) : s ≤ bound D s := by unfold bound; omega
theorem one_le_bound (D s : ℕ) : 1 ≤ bound D s := by unfold bound; omega

private theorem factor_le (D : ℕ) : D-1 ≤ (D+1)*(2^D+3) := by
  have := Nat.zero_le (2^D)
  nlinarith [Nat.sub_le D 1]

private theorem target_factor_le (D : ℕ) : 2^D*(D-1) ≤ (D+1)*(2^D+3) := by
  rw [Nat.mul_comm (2^D)]
  exact Nat.mul_le_mul (by omega) (by omega)

variable {K : Type} [Field K] [DecidableEq K] {D h s : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (cC : StableFree.Coordinates C)
  (b : ∀ j : Fin (D-1), LaurentArithmetic.DenseMatrix K D (cC.rank (j.val+1))
    (cC.rank ((j.val:ℤ)+1-1)) h)
  (d : ∀ j : Fin (D-1), LaurentArithmetic.DenseMatrix K D (cC.rank ((j.val:ℤ)+1+1))
    (cC.rank (j.val+1)) h)

theorem layer_cost_bound (hr : ∀ j : ℤ, cC.rank j ≤ s) (hh : h ≤ s) :
    (storedLayersProgram cC b d).cost ≤ (D-1)*AlgorithmTwoCohomologyGrowth.bound D s := by
  rw [storedLayersProgram_cost, layerProgram_cost]
  calc
    _ ≤ ∑ _j : Fin (D-1), AlgorithmTwoCohomologyGrowth.bound D s := by
      apply Finset.sum_le_sum
      intro j _
      exact (AlgorithmTwoCohomology.compute_cost (b j) (d j)).trans
        (costBound_le (hr _) (hr _) (hr _) hh)
    _ = _ := by simp

theorem layer_cost_polynomial (hr : ∀ j : ℤ, cC.rank j ≤ s) (hh : h ≤ s) :
    (storedLayersProgram cC b d).cost ≤ (polynomial D).eval s := by
  rw [polynomial_eval]
  apply (layer_cost_bound cC b d hr hh).trans
  have := Nat.mul_le_mul_right (AlgorithmTwoCohomologyGrowth.bound D s) (factor_le D)
  unfold bound
  omega

variable {cC b d}

theorem dimension_le (out : StoredLayers cC b d) (hr : ∀ j : ℤ, cC.rank j ≤ s)
    (hh : h ≤ s) (j : Fin (D-1)) :
    out.multiplicities.get j ≤ AlgorithmTwoCohomologyGrowth.bound D s := by
  rw [StoredLayers.multiplicities_correct]
  exact compute_dimension_bound (b j) (d j) (hr _) (hr _) hh

theorem copies_le (out : StoredLayers cC b d) (hr : ∀ j : ℤ, cC.rank j ≤ s)
    (hh : h ≤ s) :
    (∑ j : Fin (D-1), out.multiplicities.get j) ≤
      (D-1)*AlgorithmTwoCohomologyGrowth.bound D s := by
  calc
    _ ≤ ∑ _j : Fin (D-1), AlgorithmTwoCohomologyGrowth.bound D s :=
      Finset.sum_le_sum fun j _ => dimension_le out hr hh j
    _ = _ := by simp

theorem target_rank_le (out : StoredLayers cC b d) (hr : ∀ j : ℤ, cC.rank j ≤ s)
    (hh : h ≤ s) :
    2^D*(∑ j : Fin (D-1), out.multiplicities.get j) ≤ bound D s := by
  have hcopies := Nat.mul_le_mul_left (2^D) (copies_le out hr hh)
  have hfactor := Nat.mul_le_mul_right (AlgorithmTwoCohomologyGrowth.bound D s) (target_factor_le D)
  have ht : 2^D*((D-1)*AlgorithmTwoCohomologyGrowth.bound D s) =
      (2^D*(D-1))*AlgorithmTwoCohomologyGrowth.bound D s := by ring
  rw [ht] at hcopies
  unfold bound
  omega

theorem top_count_le (out : StoredLayers cC b d) (hr : ∀ j : ℤ, cC.rank j ≤ s)
    (hh : h ≤ s) :
    (∑ j : Fin (D-1), out.multiplicities.get j) ≤ bound D s := by
  have := copies_le out hr hh
  have := Nat.mul_le_mul_right (AlgorithmTwoCohomologyGrowth.bound D s) (factor_le D)
  unfold bound
  omega

theorem commonRadius_le (out : StoredLayers cC b d) (hr : ∀ j : ℤ, cC.rank j ≤ s)
    (hh : h ≤ s) : out.commonRadius ≤ bound D s := by
  have hrad := out.commonRadius_bound (AlgorithmTwoCohomologyGrowth.bound D s)
    (fun j => compute_radius_bound (hr _) hh)
  have := Nat.mul_le_mul_right (AlgorithmTwoCohomologyGrowth.bound D s) (factor_le D)
  unfold bound
  omega

end Decoupling.HighDim.AlgorithmTwoLayersGrowth
