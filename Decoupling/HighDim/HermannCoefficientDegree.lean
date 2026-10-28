import Decoupling.HighDim.HermannCoefficientReduction
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# Total-degree accounting for last-variable coefficient reduction

The smaller system's entries are actual coefficients of the input, so their
total degree does not increase. Reassembly adds at most the last-variable
cutoff minus one. These estimates supply the induction's degree recurrence.
-/

namespace Decoupling.HighDim.Hermann
open MvPolynomial Matrix
noncomputable section
variable {K : Type*} [CommRing K] {N m n : ℕ}

/-- Total-degree bounds can be checked coefficient by coefficient, with
the removed variable's exponent retained in the weight. -/
theorem totalDegree_finSucc_symm_le (P : Polynomial (MvPolynomial (Fin N) K)) (B : ℕ)
    (h : ∀ i, P.coeff i ≠ 0 → (P.coeff i).totalDegree + i ≤ B) :
    ((MvPolynomial.finSuccEquiv K N).symm P).totalDegree ≤ B := by
  classical
  apply Finset.sup_le
  intro a ha
  have hc : (P.coeff (a 0)).coeff a.tail ≠ 0 := by
    have hh := MvPolynomial.finSuccEquiv_coeff_coeff a.tail
      ((MvPolynomial.finSuccEquiv K N).symm P) (a 0)
    rw [AlgEquiv.apply_symm_apply, Finsupp.cons_tail] at hh
    rw [hh]
    exact MvPolynomial.mem_support_iff.mp ha
  have hp : P.coeff (a 0) ≠ 0 := by intro hp; simp [hp] at hc
  have hsum : a.sum (fun _ k => k) = a.tail.sum (fun _ k => k) + a 0 := by
    conv_lhs => rw [← Finsupp.cons_tail a]
    rw [Finsupp.sum_cons]
    exact Nat.add_comm _ _
  change a.sum (fun _ k => k) ≤ B
  rw [hsum]
  exact (Nat.add_le_add_right
    (MvPolynomial.le_totalDegree (MvPolynomial.mem_support_iff.mpr hc)) (a 0)).trans (h _ hp)

/-- Coefficients over the smaller polynomial ring retain the original degree bound. -/
theorem finSucc_coefficient_totalDegree_le (P : MvPolynomial (Fin (N + 1)) K)
    (d : ℕ) (hP : P.totalDegree ≤ d) (i : ℕ) :
    ((MvPolynomial.finSuccEquiv K N P).coeff i).totalDegree ≤ d := by
  by_cases hi : (MvPolynomial.finSuccEquiv K N P).coeff i = 0
  · simp [hi]
  · exact (Nat.le_add_right _ _).trans
      ((MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le P i hi).trans hP)

/-- Every actual entry in the lower-variable coefficient matrix has the
same total-degree bound as the original matrix entries. -/
theorem lastCoefficientMatrix_totalDegree_le
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin (N + 1)) K)) (d b : ℕ)
    (hA : ∀ i j, (A i j).totalDegree ≤ d)
    (i : Fin m × Fin (d + b)) (j : Fin n × Fin b) :
    (lastCoefficientMatrix (A.map (MvPolynomial.finSuccEquiv K N)) d b i j).totalDegree ≤ d := by
  unfold lastCoefficientMatrix
  split
  · exact finSucc_coefficient_totalDegree_le (A i.1 j.1) d (hA i.1 j.1) _
  · simp

/-- Reassembling bounded smaller-variable coefficients adds only b-1 to
the total-degree budget, including the empty cutoff b=0. -/
theorem lastEncode_totalDegree_le (b B : ℕ)
    (z : (Fin n × Fin b) → MvPolynomial (Fin N) K)
    (hz : ∀ j, (z j).totalDegree ≤ B) (j : Fin n) :
    ((MvPolynomial.finSuccEquiv K N).symm (lastEncode b z j)).totalDegree ≤ B + (b - 1) := by
  apply totalDegree_finSucc_symm_le
  intro i hi
  have hib : i < b := by
    by_contra hn
    have he : (lastEncode b z j).degree < (i : WithBot ℕ) :=
      (lastEncode_degree b z j).trans_le (by exact_mod_cast (Nat.le_of_not_gt hn))
    exact hi (Polynomial.coeff_eq_zero_of_degree_lt he)
  have hc : (lastEncode b z j).coeff i = z (j, ⟨i, hib⟩) :=
    congrFun (lastDecode_encode b z) (j, ⟨i, hib⟩)
  rw [hc]
  exact Nat.add_le_add (hz _) (Nat.le_sub_one_of_lt hib)

end
end Decoupling.HighDim.Hermann
