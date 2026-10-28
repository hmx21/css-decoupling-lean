import Mathlib.Tactic

/-!
# The quantitative recurrence in Hermann elimination

This file proves arithmetic bounds for the recurrence arising from actual
one-variable elimination. It does not assert that the recurrence bounds
solutions until the mathematical elimination induction is connected.
The explicit upper bound is exactly the expression cited in C5.
-/

namespace Decoupling.HighDim.Hermann

/-- The coefficient-comparison system has at most d*m*(m+1) equations. -/
def nextRows (m d : ℕ) : ℕ := d * m * (m + 1)

/-- A degree budget from eliminating one polynomial variable at a time. -/
def recurrenceBound : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | N + 1, m, d => recurrenceBound N (nextRows m d) d + m * d

/-- The published homogeneous/inhomogeneous degree-bound expression. -/
def hermannBound (N m d : ℕ) : ℕ := (2 * m * d) ^ (2 ^ N)

@[simp] theorem recurrenceBound_zero_rows (N d : ℕ) : recurrenceBound N 0 d = 0 := by
  induction N with
  | zero => rfl
  | succ N ih => simpa only [recurrenceBound, nextRows, mul_zero, zero_mul, add_zero] using ih

@[simp] theorem recurrenceBound_zero_degree (N m : ℕ) : recurrenceBound N m 0 = 0 := by
  cases N with
  | zero => rfl
  | succ N => simp [recurrenceBound, nextRows]

theorem nextRows_mono {m m' d d' : ℕ} (hm : m ≤ m') (hd : d ≤ d') :
    nextRows m d ≤ nextRows m' d' :=
  Nat.mul_le_mul (Nat.mul_le_mul hd hm) (Nat.add_le_add_right hm 1)

theorem recurrenceBound_mono (N : ℕ) {m m' d d' : ℕ} (hm : m ≤ m') (hd : d ≤ d') :
    recurrenceBound N m d ≤ recurrenceBound N m' d' := by
  induction N generalizing m m' d d' with
  | zero => exact le_rfl
  | succ N ih =>
    exact Nat.add_le_add (ih (nextRows_mono hm hd) hd) (Nat.mul_le_mul hm hd)

/-- The slack term makes the recurrence estimate valid at every induction step. -/
theorem recurrenceBound_add_le (N m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    recurrenceBound N m d + 2 * m * d ≤ hermannBound N m d := by
  induction N generalizing m with
  | zero => simp [recurrenceBound, hermannBound]
  | succ N ih =>
    have hnext : 1 ≤ nextRows m d := by
      have hpos : 0 < nextRows m d := by dsimp [nextRows]; positivity
      omega
    have hslack : m * d + 2 * m * d ≤ 2 * nextRows m d * d := by
      dsimp [nextRows]
      nlinarith [Nat.mul_le_mul hm hd]
    have hsq : 2 * nextRows m d * d ≤ (2 * m * d) ^ 2 := by
      dsimp [nextRows]
      nlinarith [Nat.mul_self_le_mul_self hm]
    calc
      recurrenceBound (N + 1) m d + 2 * m * d =
          recurrenceBound N (nextRows m d) d + (m * d + 2 * m * d) := by
            simp only [recurrenceBound, Nat.add_assoc]
      _ ≤ recurrenceBound N (nextRows m d) d + 2 * nextRows m d * d :=
        Nat.add_le_add_left hslack _
      _ ≤ hermannBound N (nextRows m d) d := ih (nextRows m d) hnext
      _ ≤ ((2 * m * d) ^ 2) ^ (2 ^ N) := Nat.pow_le_pow_left hsq _
      _ = hermannBound (N + 1) m d := by
        unfold hermannBound
        rw [← pow_mul]
        congr 1
        simp [pow_succ, Nat.mul_comm]

/-- All degenerate cases are included: zero rows and degree zero give budget zero. -/
theorem recurrenceBound_le (N m d : ℕ) : recurrenceBound N m d ≤ hermannBound N m d := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hd : d = 0
  · simp [hd]
  exact (Nat.le_add_right _ _).trans
    (recurrenceBound_add_le N m d (by omega) (by omega))

end Decoupling.HighDim.Hermann
