import Decoupling.HighDim.HermannMinor
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# The actual minor-based syzygy matrix

For an r-by-n matrix A and an injectively selected r-by-r minor Δ, construct
E = det(Δ) I - J adj(Δ) A. Its columns are genuine syzygies, and E acts as
multiplication by det(Δ) on the whole kernel. The degree of every entry is
at most r times the degree of A. Reducing all coordinates by det(Δ) therefore
implements Hermann elimination without imposing a coordinate-complement choice.
-/

namespace Decoupling.HighDim.Hermann
open Matrix MvPolynomial
noncomputable section
variable {S : Type*} [CommRing S] {r n : ℕ}

/-- Insert the selected coordinates, with literal zero entries elsewhere. -/
def columnInclusion (cols : Fin r ↪ Fin n) : Matrix (Fin n) (Fin r) S :=
  fun j i => if j = cols i then 1 else 0

theorem mul_columnInclusion (A : Matrix (Fin r) (Fin n) S) (cols : Fin r ↪ Fin n) :
    A * columnInclusion cols = A.submatrix id cols := by
  ext i j
  simp [Matrix.mul_apply, columnInclusion]

/-- A matrix of n actual homogeneous solutions. -/
def syzygyMatrix (A : Matrix (Fin r) (Fin n) S) (cols : Fin r ↪ Fin n) :
    Matrix (Fin n) (Fin n) S :=
  (A.submatrix id cols).det • 1 - columnInclusion cols * (A.submatrix id cols).adjugate * A

theorem mul_syzygyMatrix (A : Matrix (Fin r) (Fin n) S) (cols : Fin r ↪ Fin n) :
    A * syzygyMatrix A cols = 0 := by
  rw [syzygyMatrix, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    ← Matrix.mul_assoc A, ← Matrix.mul_assoc A, mul_columnInclusion,
    Matrix.mul_adjugate, Matrix.smul_mul, Matrix.one_mul, sub_self]

/-- On actual solutions the syzygy matrix is multiplication by the minor. -/
theorem syzygyMatrix_on_kernel (A : Matrix (Fin r) (Fin n) S) (cols : Fin r ↪ Fin n)
    (y : Fin n → S) (hy : A *ᵥ y = 0) :
    syzygyMatrix A cols *ᵥ y = (A.submatrix id cols).det • y := by
  rw [syzygyMatrix, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero, sub_zero]

variable {K : Type*} [CommRing K] {σ : Type*}

/-- Total-degree determinant bound over the actual multivariate polynomial ring. -/
theorem determinant_totalDegree_le
    (A : Matrix (Fin r) (Fin r) (MvPolynomial σ K)) (d : ℕ)
    (hA : ∀ i j, (A i j).totalDegree ≤ d) : A.det.totalDegree ≤ r * d := by
  classical
  rw [Matrix.det_apply]
  apply MvPolynomial.totalDegree_finsetSum_le
  intro s _
  have hs : (Equiv.Perm.sign s • ∏ i, A (s i) i).totalDegree =
      (∏ i, A (s i) i).totalDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
    · simp [h]
    · simp [h, Units.neg_smul]
  rw [hs]
  apply (MvPolynomial.totalDegree_finsetProd _ _).trans
  calc
    ∑ i : Fin r, (A (s i) i).totalDegree ≤ ∑ _i : Fin r, d :=
      Finset.sum_le_sum (fun i _ => hA (s i) i)
    _ = r * d := by simp

theorem adjugate_mul_totalDegree_le
    (A : Matrix (Fin r) (Fin r) (MvPolynomial σ K))
    (B : Matrix (Fin r) (Fin n) (MvPolynomial σ K)) (d : ℕ)
    (hA : ∀ i j, (A i j).totalDegree ≤ d)
    (hB : ∀ i j, (B i j).totalDegree ≤ d) (i : Fin r) (j : Fin n) :
    ((A.adjugate * B) i j).totalDegree ≤ r * d := by
  have he : (A.adjugate * B) i j = (A.updateCol i (fun k => B k j)).det := by
    change (A.adjugate *ᵥ (fun k => B k j)) i = _
    rw [← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
  rw [he]
  apply determinant_totalDegree_le
  intro k l
  rw [Matrix.updateCol_apply]
  split
  · exact hB k j
  · exact hA k l

/-- The degree control applies to the actual constructed syzygy columns. -/
theorem syzygyMatrix_totalDegree_le
    (A : Matrix (Fin r) (Fin n) (MvPolynomial σ K)) (cols : Fin r ↪ Fin n)
    (d : ℕ) (hA : ∀ i j, (A i j).totalDegree ≤ d) (i j : Fin n) :
    (syzygyMatrix A cols i j).totalDegree ≤ r * d := by
  classical
  apply (MvPolynomial.totalDegree_sub _ _).trans
  apply max_le
  · by_cases hij : i = j
    · subst j
      simpa only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one] using
        determinant_totalDegree_le (A.submatrix id cols) d (fun i j => hA i (cols j))
    · simp [Matrix.smul_apply, Matrix.one_apply_ne hij]
  · rw [Matrix.mul_assoc]
    change (∑ k, columnInclusion cols i k * ((A.submatrix id cols).adjugate * A) k j).totalDegree ≤ _
    apply MvPolynomial.totalDegree_finsetSum_le
    intro k _
    unfold columnInclusion
    split
    · simpa only [one_mul] using
        adjugate_mul_totalDegree_le (A.submatrix id cols) A d (fun i j => hA i (cols j)) hA k j
    · simp

end
end Decoupling.HighDim.Hermann
