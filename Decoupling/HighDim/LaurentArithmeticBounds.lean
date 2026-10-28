import Decoupling.HighDim.LaurentArithmeticMatrix

/-!
# HD012 polynomial bounds for actual Laurent matrix operations

The bounds below apply to the already defined executable programs and
their actual traces. They are local size lemmas, not a replacement for
tracking all stages of Algorithm 2.
-/
namespace Decoupling.HighDim.LaurentArithmetic
variable {K : Type*} [Field K] {D a b m n r S : ℕ}

theorem boxSize_mono {h k : ℕ} (hk : h ≤ k) : boxSize D h ≤ boxSize D k := by
  unfold boxSize
  exact Nat.pow_le_pow_left (by omega) D

theorem boxSize_polynomial {h : ℕ} (hh : h ≤ S) :
    boxSize D h ≤ 3 ^ D * (S + 1) ^ D := by
  rw [← Nat.mul_pow]
  unfold boxSize
  exact Nat.pow_le_pow_left (by omega) D

theorem sumBoxSize_polynomial (ha : a ≤ S) (hb : b ≤ S) :
    boxSize D (a + b) ≤ 5 ^ D * (S + 1) ^ D := by
  rw [← Nat.mul_pow]
  unfold boxSize
  exact Nat.pow_le_pow_left (by omega) D

theorem matrixMulProgram_cost_polynomial
    (A : DenseMatrix K D m n a) (B : DenseMatrix K D n r b)
    (hm : m ≤ S) (hn : n ≤ S) (hr : r ≤ S) (ha : a ≤ S) (hb : b ≤ S) :
    (matrixMulProgram A B).cost ≤
      (5 ^ D * (2 * 3 ^ D + 1)) * (S + 1) ^ (3 + 2 * D) := by
  rw [matrixMulProgram_cost]
  have hp : 1 ≤ (S + 1) ^ D := Nat.one_le_pow D (S + 1) (by omega)
  calc
    _ ≤ (S + 1) * (S + 1) * (S + 1) *
        (5 ^ D * (S + 1) ^ D) * ((2 * 3 ^ D + 1) * (S + 1) ^ D) := by
      apply Nat.mul_le_mul
      · apply Nat.mul_le_mul
        · exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (by omega)
        · exact sumBoxSize_polynomial ha hb
      · have h := boxSize_polynomial (D := D) ha
        nlinarith
    _ = _ := by
      rw [show 3 + 2 * D = 3 + D + D by omega, pow_add, pow_add]
      ring

theorem matrixAddProgram_cost_polynomial
    (A : DenseMatrix K D m n a) (B : DenseMatrix K D m n b)
    (hm : m ≤ S) (hn : n ≤ S) (ha : a ≤ S) (hb : b ≤ S) :
    (matrixAddProgram A B).cost ≤ 3 ^ D * (S + 1) ^ (2 + D) := by
  rw [matrixAddProgram_cost]
  calc
    _ ≤ (S + 1) * (S + 1) * (3 ^ D * (S + 1) ^ D) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega))
        (boxSize_polynomial (max_le ha hb))
    _ = _ := by rw [pow_add]; ring

/-- Dense coefficient count of the actual product output. -/
theorem matrixMulProgram_output_size
    (hm : m ≤ S) (hr : r ≤ S) (ha : a ≤ S) (hb : b ≤ S) :
    m * r * boxSize D (a + b) ≤ 5 ^ D * (S + 1) ^ (2 + D) := by
  calc
    _ ≤ (S + 1) * (S + 1) * (5 ^ D * (S + 1) ^ D) :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega)) (sumBoxSize_polynomial ha hb)
    _ = _ := by rw [pow_add]; ring

end Decoupling.HighDim.LaurentArithmetic
