import Decoupling.HighDim.HermannMonicRay

/-!
# An infinite-field linear coordinate change with constant leading coefficient

HD012 effective Hermann reduction. This proves the coordinate-change lemma
from the actual top homogeneous component, the explicit triangular algebra
automorphism, and the actual coefficient identity along a linear ray.
It has no extra generic-position or monic-coordinate hypothesis.
-/

namespace Decoupling.HighDim.Hermann

open MvPolynomial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {N : ℕ}

/-- Setting the other variables to zero after the linear change gives the
actual ray restriction, as an equality of univariate polynomials. -/
theorem linearCoordinates_ray (v : Fin (N+1) → K) (hv : v 0 ≠ 0)
    (P : MvPolynomial (Fin (N+1)) K) :
    Polynomial.map (eval (fun _ : Fin N => (0 : K)))
      (finSuccEquiv K N (linearCoordinates v hv P)) = ray v P := by
  let f : MvPolynomial (Fin (N+1)) K →+* Polynomial K :=
    (Polynomial.mapRingHom (eval (fun _ : Fin N => (0 : K)))).comp
      ((finSuccEquiv K N).toRingHom.comp (linearCoordinates v hv).toRingHom)
  have he : f = (ray v).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [f, linearCoordinates, forwardSubstitution, ray,
        MvPolynomial.algebraMap_eq, finSuccEquiv_apply]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [f, linearCoordinates, forwardSubstitution, forwardForm, ray,
          finSuccEquiv_apply]
      · simp [f, linearCoordinates, forwardSubstitution, forwardForm, ray,
          finSuccEquiv_apply]
  exact RingHom.congr_fun he P

/-- At the total-degree bound the leading-variable coefficient is a constant.
This includes a zero coefficient and needs no nonvanishing premise. -/
theorem finSucc_topCoeff_constant (P : MvPolynomial (Fin (N+1)) K) (d : ℕ)
    (hP : P.totalDegree ≤ d) :
    (finSuccEquiv K N P).coeff d =
      C (eval (fun _ : Fin N => (0 : K)) ((finSuccEquiv K N P).coeff d)) := by
  by_cases hc : (finSuccEquiv K N P).coeff d = 0
  · simp [hc]
  · have hd := totalDegree_coeff_finSuccEquiv_add_le P d hc
    have hz : ((finSuccEquiv K N P).coeff d).totalDegree = 0 := by omega
    simpa only [eval_zero', constantCoeff_eq] using
      (totalDegree_eq_zero_iff_eq_C.mp hz)

/-- The coefficient at degree `totalDegree P` is exactly the evaluated
highest homogeneous component, hence is a nonzero constant in the chosen direction. -/
theorem linearCoordinates_topCoeff (v : Fin (N+1) → K) (hv : v 0 ≠ 0)
    (P : MvPolynomial (Fin (N+1)) K) :
    (finSuccEquiv K N (linearCoordinates v hv P)).coeff P.totalDegree =
      C (eval v (homogeneousComponent P.totalDegree P)) := by
  have hc := congrArg (fun Q : Polynomial K => Q.coeff P.totalDegree)
    (linearCoordinates_ray v hv P)
  rw [Polynomial.coeff_map, ray_coeff] at hc
  rw [finSucc_topCoeff_constant _ P.totalDegree
    (linearCoordinates_totalDegree v hv P).le, hc]

/-- The exact monic-coordinate interface for Hermann induction. Only the
infinite field and nonzero input polynomial are hypotheses. -/
theorem exists_linear_monic_coordinates [Infinite K] (N : ℕ)
    (P : MvPolynomial (Fin (N+1)) K) (hP : P ≠ 0) :
    ∃ e : MvPolynomial (Fin (N+1)) K ≃ₐ[K] MvPolynomial (Fin (N+1)) K,
      (∀ Q, (e Q).totalDegree = Q.totalDegree) ∧
      ∃ u : Kˣ, (finSuccEquiv K N (e P)).leadingCoeff = C (u : K) ∧
        (finSuccEquiv K N (e P)).natDegree = P.totalDegree := by
  obtain ⟨v,hv,hH⟩ := exists_top_direction N P hP
  let e := linearCoordinates v hv
  let c := eval v (homogeneousComponent P.totalDegree P)
  have hc : c ≠ 0 := hH
  have hcoeff : (finSuccEquiv K N (e P)).coeff P.totalDegree = C c :=
    linearCoordinates_topCoeff v hv P
  have hcn : (finSuccEquiv K N (e P)).coeff P.totalDegree ≠ 0 := by
    rw [hcoeff]
    exact C_ne_zero.mpr hc
  have hdegree : (finSuccEquiv K N (e P)).natDegree = P.totalDegree := by
    apply le_antisymm
    · rw [natDegree_finSuccEquiv]
      exact (degreeOf_le_totalDegree (e P) 0).trans (linearCoordinates_totalDegree v hv P).le
    · exact Polynomial.le_natDegree_of_ne_zero hcn
  refine ⟨e, linearCoordinates_totalDegree v hv, Units.mk0 c hc, ?_, hdegree⟩
  change (finSuccEquiv K N (e P)).coeff (finSuccEquiv K N (e P)).natDegree = C c
  rw [hdegree, hcoeff]

end
end Decoupling.HighDim.Hermann
