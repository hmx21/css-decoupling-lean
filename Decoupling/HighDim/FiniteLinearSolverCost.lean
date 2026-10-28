import Decoupling.HighDim.FiniteLinearSolverCorrectness

/-!
# Polynomial length of the actual Gaussian operation trace

The bounds count the operations emitted by the executed program, even
on inconsistent systems. Zero tests are included. Integer indexing,
array copying, and bit complexity are not field arithmetic operations.
-/
namespace Decoupling.HighDim.FiniteLinearSolver
open ArithmeticCost
universe u
variable {K : Type u} [Field K] [DecidableEq K]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

omit [DecidableEq K] in
@[simp] theorem eliminateProgram_cost {m n : ℕ} (A : DenseMatrix K m (n + 1)) (b : Vector K m)
    (r : Fin m) : (eliminateProgram A b r).cost = m * (2 * n + 3) := by
  simp only [eliminateProgram, Work.bind_cost, collect_cost, mul_cost, sub_cost, div_cost,
    Work.pure_cost, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

omit [DecidableEq K] in
@[simp] theorem pivotProgram_cost {m n : ℕ} (A : DenseMatrix K m (n + 1)) (b : Vector K m)
    (r : Fin m) (s : Solution K n) :
    (pivotProgram A b r s).cost = (2 * n + 2) * (s.dimension + 1) := by
  simp only [pivotProgram, Work.bind_cost, collect_cost, dot_cost, sub_cost, div_cost,
    neg_cost, Work.pure_cost, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

theorem arithmetic_step_bound (m n k : ℕ) (hk : k ≤ n) :
    m + m * (2 * n + 3) + (2 * n + 2) * (k + 1) ≤ 8 * (m + 1) * (n + 1) ^ 2 := by
  have hmul := Nat.mul_le_mul_left (2 * n + 2) (Nat.add_le_add_right hk 1)
  nlinarith [Nat.zero_le (m * n * n), Nat.zero_le (m * n), Nat.zero_le (n * n)]

theorem arithmetic_advance_bound (m n : ℕ) :
    8 * (m + 1) * (n + 1) ^ 3 + 8 * (m + 1) * (n + 1) ^ 2 ≤
      8 * (m + 1) * (n + 2) ^ 3 := by
  have h : (n + 1) ^ 3 + (n + 1) ^ 2 ≤ (n + 2) ^ 3 := by
    calc
      _ ≤ (n + 1) ^ 3 + (n + 1) ^ 2 + (2 * n ^ 2 + 7 * n + 6) := Nat.le_add_right _ _
      _ = (n + 2) ^ 3 := by ring
  simpa only [Nat.mul_add] using Nat.mul_le_mul_left (8 * (m + 1)) h

/-- Uniform bound on the trace of the actual terminating program. -/
theorem gaussian_cost_le : ∀ (n : ℕ) {m : ℕ} (A : DenseMatrix K m n) (b : Vector K m),
    (gaussian n A b).cost ≤ 8 * (m + 1) * (n + 1) ^ 3 := by
  intro n
  induction n with
  | zero =>
    intro m A b
    simp only [gaussian, Work.bind_cost, Work.pure_cost, add_zero]
    have h := firstNonzero_cost m (vector b)
    nlinarith
  | succ n ih =>
    intro m A b
    change (gaussian (n + 1) A b).cost ≤ 8 * (m + 1) * (n + 2) ^ 3
    have hscan := firstNonzero_cost m (fun i => A[i][0])
    have hadv := arithmetic_advance_bound m n
    simp only [gaussian, Work.bind_cost]
    cases hpiv : (firstNonzero m (fun i => A[i][0])).value with
    | none =>
      simp only [Work.bind_cost, Work.pure_cost, add_zero]
      have hr := ih (tailMatrix A) b
      have hs := arithmetic_step_bound m n 0 (Nat.zero_le n)
      omega
    | some r =>
      simp only [Work.bind_cost, eliminateProgram_value, eliminateProgram_cost]
      have hr := ih (eliminatedMatrix A r) (eliminatedRhs A b r)
      cases hres : (gaussian n (eliminatedMatrix A r) (eliminatedRhs A b r)).value with
      | none =>
        simp only [Work.pure_cost]
        have hs := arithmetic_step_bound m n 0 (Nat.zero_le n)
        omega
      | some s =>
        simp only [Work.bind_cost, Work.pure_cost, pivotProgram_cost]
        have hd := (gaussian_correct (eliminatedMatrix A r) (eliminatedRhs A b r) s hres).dimension_le
        have hs := arithmetic_step_bound m n s.dimension hd
        omega

/-- A single polynomial in the matrix dimensions bounds every field
operation and zero test, independently of the field's cardinality. -/
theorem gaussian_cost_polynomial {m n : ℕ} (A : DenseMatrix K m n) (b : Vector K m) :
    (gaussian n A b).cost ≤ 8 * (m + n + 1) ^ 4 := by
  calc
    _ ≤ 8 * (m + 1) * (n + 1) ^ 3 := gaussian_cost_le n A b
    _ ≤ 8 * (m + n + 1) * (m + n + 1) ^ 3 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 8 (by omega)) (Nat.pow_le_pow_left (by omega) 3)
    _ = 8 * (m + n + 1) ^ 4 := by ring

end Decoupling.HighDim.FiniteLinearSolver
