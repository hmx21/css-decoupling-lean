import Decoupling.HighDim.HermannMonicLinear

/-!
# The actual highest coefficient on a linear ray

The coefficient of `t^d` in `P(v t)` is the evaluation at `v` of the
actual homogeneous component of degree `d`. An infinite coefficient field
then supplies a direction with nonzero first coordinate and nonvanishing
highest homogeneous component. No generic-coordinate premise is assumed.
-/

namespace Decoupling.HighDim.Hermann

open MvPolynomial
noncomputable section
variable {K : Type*} [Field K] {σ : Type*}

/-- Restrict a multivariate polynomial to the actual linear ray `t ↦ v t`. -/
def ray (v : σ → K) : MvPolynomial σ K →ₐ[K] Polynomial K :=
  aeval (fun i => Polynomial.C (v i) * Polynomial.X)

theorem ray_monomial (v : σ → K) (s : σ →₀ ℕ) (c : K) :
    ray v (monomial s c) =
      Polynomial.monomial s.degree (c * s.prod (fun i k => v i ^ k)) := by
  classical
  rw [ray, aeval_monomial]
  change Polynomial.C c * (∏ i ∈ s.support,
    (Polynomial.C (v i) * Polynomial.X) ^ s i) = _
  simp_rw [mul_pow, ← map_pow]
  rw [Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum,
    ← mul_assoc, ← map_mul, Polynomial.C_mul_X_pow_eq_monomial]
  rfl

/-- An equality of actual coefficients, including the zero/constant cases. -/
theorem ray_coeff (v : σ → K) (P : MvPolynomial σ K) (d : ℕ) :
    (ray v P).coeff d = eval v (homogeneousComponent d P) := by
  classical
  induction P using MvPolynomial.induction_on' with
  | monomial s c =>
      rw [ray_monomial, Polynomial.coeff_monomial,
        homogeneousComponent_of_mem (isHomogeneous_monomial c rfl)]
      by_cases h : s.degree = d
      · simp [h, eval_monomial]
      · simp [h, Ne.symm h]
  | add P Q hP hQ =>
      simp only [map_add, Polynomial.coeff_add, hP, hQ]

/-- A nonzero polynomial has a nonzero highest homogeneous component. -/
theorem topComponent_ne_zero (P : MvPolynomial σ K) (hP : P ≠ 0) :
    homogeneousComponent P.totalDegree P ≠ 0 := by
  classical
  obtain ⟨s, hs, hd⟩ := P.support.exists_mem_eq_sup
    (by
      obtain ⟨s, hs⟩ := exists_coeff_ne_zero hP
      exact ⟨s, mem_support_iff.mpr hs⟩)
    (fun s : σ →₀ ℕ => s.degree)
  have hd' : s.degree = P.totalDegree := hd.symm
  intro hz
  have hh := congrArg (fun Q : MvPolynomial σ K => Q.coeff s) hz
  rw [coeff_homogeneousComponent, ite_eq_left hd', AddMonoidAlgebra.coeff_zero] at hh
  exact (mem_support_iff.mp hs) hh

/-- Nonvanishing at one direction is proved from infinitude, applied to
`X₀` times the highest homogeneous component, so the first entry is nonzero. -/
theorem exists_top_direction [Infinite K] (N : ℕ)
    (P : MvPolynomial (Fin (N+1)) K) (hP : P ≠ 0) :
    ∃ v : Fin (N+1) → K, v 0 ≠ 0 ∧
      eval v (homogeneousComponent P.totalDegree P) ≠ 0 := by
  let H := homogeneousComponent P.totalDegree P
  have hH : H ≠ 0 := topComponent_ne_zero P hP
  have hprod : H * X (0 : Fin (N+1)) ≠ 0 := mul_ne_zero hH (X_ne_zero _)
  have hhom : (H * X (0 : Fin (N+1))).IsHomogeneous (P.totalDegree + 1) :=
    (homogeneousComponent_isHomogeneous _ P).mul (isHomogeneous_X K _)
  have hv : ∃ v : Fin (N+1) → K, eval v (H * X (0 : Fin (N+1))) ≠ 0 := by
    by_contra h
    push Not at h
    exact hprod (hhom.eq_zero_of_forall_eval_eq_zero h)
  obtain ⟨v,hv⟩ := hv
  rw [map_mul, eval_X] at hv
  exact ⟨v, (mul_ne_zero_iff.mp hv).2, (mul_ne_zero_iff.mp hv).1⟩

end
end Decoupling.HighDim.Hermann
