import Decoupling.HighDim.HermannBounds

/-!
# A conservative common degree budget for inhomogeneous elimination

The additional lift after polynomial division costs at most 2*m*d in total
degree. This wider recurrence has upper bound (4*m*d)^(2^N), still a fixed-N
polynomial and sufficient for Proposition 1. No claim of sharpness is made.
This is arithmetic accounting; the actual-system theorem is proved separately.
-/

namespace Decoupling.HighDim.Hermann

def solutionBound : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | N + 1, m, d => solutionBound N (nextRows m d) d + 2 * m * d

@[simp] theorem solutionBound_zero_rows (N d : ℕ) : solutionBound N 0 d = 0 := by
  induction N with
  | zero => rfl
  | succ N ih => simpa only [solutionBound, nextRows, mul_zero, zero_mul, add_zero] using ih

@[simp] theorem solutionBound_zero_degree (N m : ℕ) : solutionBound N m 0 = 0 := by
  cases N with
  | zero => rfl
  | succ N => simp [solutionBound, nextRows]

theorem solutionBound_mono (N : ℕ) {m m' d d' : ℕ} (hm : m ≤ m') (hd : d ≤ d') :
    solutionBound N m d ≤ solutionBound N m' d' := by
  induction N generalizing m m' d d' with
  | zero => exact le_rfl
  | succ N ih =>
    exact Nat.add_le_add (ih (nextRows_mono hm hd) hd)
      (Nat.mul_le_mul (Nat.mul_le_mul_left 2 hm) hd)

theorem solutionBound_add_le (N m d : ℕ) (hm : 1 ≤ m) (hd : 1 ≤ d) :
    solutionBound N m d + 4 * m * d ≤ (4 * m * d) ^ (2 ^ N) := by
  induction N generalizing m with
  | zero => simp [solutionBound]
  | succ N ih =>
    have hnext : 1 ≤ nextRows m d := by
      have hp : 0 < nextRows m d := by dsimp [nextRows]; positivity
      omega
    have hslack : 2 * m * d + 4 * m * d ≤ 4 * nextRows m d * d := by
      dsimp [nextRows]
      nlinarith [Nat.mul_le_mul hm hd]
    have hsq : 4 * nextRows m d * d ≤ (4 * m * d) ^ 2 := by
      dsimp [nextRows]
      nlinarith [Nat.mul_self_le_mul_self hm]
    calc
      solutionBound (N + 1) m d + 4 * m * d =
          solutionBound N (nextRows m d) d + (2 * m * d + 4 * m * d) := by
            simp only [solutionBound, Nat.add_assoc]
      _ ≤ solutionBound N (nextRows m d) d + 4 * nextRows m d * d := Nat.add_le_add_left hslack _
      _ ≤ (4 * nextRows m d * d) ^ (2 ^ N) := ih _ hnext
      _ ≤ ((4 * m * d) ^ 2) ^ (2 ^ N) := Nat.pow_le_pow_left hsq _
      _ = (4 * m * d) ^ (2 ^ (N + 1)) := by
        rw [← pow_mul]
        congr 1
        simp [pow_succ, Nat.mul_comm]

theorem solutionBound_le (N m d : ℕ) :
    solutionBound N m d ≤ (4 * m * d) ^ (2 ^ N) := by
  by_cases hm : m = 0
  · simp [hm]
  by_cases hd : d = 0
  · simp [hd]
  exact (Nat.le_add_right _ _).trans (solutionBound_add_le N m d (by omega) (by omega))

theorem recurrenceBound_le_solutionBound (N m d : ℕ) : recurrenceBound N m d ≤ solutionBound N m d := by
  induction N generalizing m with
  | zero => exact le_rfl
  | succ N ih =>
    exact Nat.add_le_add (ih _) (by nlinarith)

end Decoupling.HighDim.Hermann
