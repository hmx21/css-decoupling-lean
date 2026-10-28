import Decoupling.HighDim.LaurentLinearSolverIndex
import Decoupling.HighDim.EffectiveLinearCompleteness

/-!
# Zero-field-operation dense positive/negative lifting

Each canonical split exponent has at most one source Laurent exponent.
The executed lift consequently uses only exponent comparisons and a lookup
in the explicit dense input. The proof identifies it with the canonical
lift used in the exact Laurent-to-polynomial system theorem.
-/

namespace Decoupling.HighDim.LaurentLinearSolver
open Matrix MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D h : ℕ}

/-- The canonical lift is additive; no multiplicative lift is asserted. -/
noncomputable def liftLinear : Laurent K D →ₗ[K] LaurentPresentation.Poly K D :=
  (Finsupp.lsum K (fun a => MvPolynomial.monomial (LaurentPresentation.liftExponent D a))).comp
    (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap

@[simp] theorem liftLinear_apply (f : Laurent K D) :
    liftLinear f = LaurentPresentation.liftPolynomial D K f := rfl

@[simp] theorem liftLinear_single (a : Translation D) (c : K) :
    liftLinear (AddMonoidAlgebra.single a c) =
      MvPolynomial.monomial (LaurentPresentation.liftExponent D a) c := by
  simp [liftLinear]

theorem indexedLift_denote (v : LaurentArithmetic.Dense K D h) :
    LaurentPresentation.variableEquiv (LaurentPresentation.liftPolynomial D K (LaurentArithmetic.denote v)) =
      ∑ k, MvPolynomial.monomial (splitExponent D (LaurentArithmetic.exponentAt D h k)) v[k] := by
  rw [← liftLinear_apply, LaurentArithmetic.denote, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [liftLinear_single, variableEquiv_lift_monomial]

/-- A direct coefficient lookup, with no field arithmetic or field equality test. -/
def liftLookup (v : LaurentArithmetic.Dense K D h) (a : Fin (D + D) →₀ ℕ) : K :=
  if splitExponent D (joinExponent D a) = a then LaurentArithmetic.lookup v (joinExponent D a) else 0

theorem liftLookup_eq_coeff (v : LaurentArithmetic.Dense K D h) (a : Fin (D + D) →₀ ℕ) :
    liftLookup v a = (LaurentPresentation.variableEquiv
      (LaurentPresentation.liftPolynomial D K (LaurentArithmetic.denote v))).coeff a := by
  classical
  rw [indexedLift_denote, MvPolynomial.coeff_sum]
  by_cases hc : splitExponent D (joinExponent D a) = a
  · rw [liftLookup, ite_eq_left hc]
    by_cases ha : joinExponent D a ∈ LaurentBoxes.box D h
    · rw [LaurentArithmetic.lookup, dite_eq_left ha]
      symm
      rw [Finset.sum_eq_single (LaurentArithmetic.exponentIndex (joinExponent D a) ha)]
      · rw [LaurentArithmetic.exponentAt_index, hc]
        simp
      · intro k _ hk
        have he : splitExponent D (LaurentArithmetic.exponentAt D h k) ≠ a := by
          intro he
          have hh := congrArg (joinExponent D) he
          rw [join_split] at hh
          apply hk
          apply LaurentArithmetic.exponentAt_injective D h
          rw [hh, LaurentArithmetic.exponentAt_index]
        simp [MvPolynomial.coeff_monomial, he]
      · simp
    · rw [LaurentArithmetic.lookup, dite_eq_right ha]
      symm
      apply Finset.sum_eq_zero
      intro k _
      have he : splitExponent D (LaurentArithmetic.exponentAt D h k) ≠ a := by
        intro he
        have hh := congrArg (joinExponent D) he
        rw [join_split] at hh
        exact ha (hh ▸ LaurentArithmetic.exponentAt_mem D h k)
      simp [MvPolynomial.coeff_monomial, he]
  · rw [liftLookup, ite_eq_right hc]
    symm
    apply Finset.sum_eq_zero
    intro k _
    have he : splitExponent D (LaurentArithmetic.exponentAt D h k) ≠ a := by
      intro he
      have hh := congrArg (joinExponent D) he
      rw [join_split] at hh
      apply hc
      rw [← hh]
      exact he
    simp [MvPolynomial.coeff_monomial, he]

/-- Materialize the lift by reading each canonical coefficient once. -/
def liftDense (d : ℕ) (v : LaurentArithmetic.Dense K D h) :
    Vector K (PolynomialLinearSolver.boxSize (D + D) d) :=
  Vector.ofFn fun k => liftLookup v (PolynomialLinearSolver.exponentAt (D + D) d k).val

/-- General uniqueness of a boxed polynomial from its explicitly enumerated coefficients. -/
theorem polynomialDenote_eq_of_coeff {N d : ℕ}
    (v : Vector K (PolynomialLinearSolver.boxSize N d)) (P : MvPolynomial (Fin N) K)
    (hP : P ∈ MvPolynomial.restrictDegree (Fin N) K d)
    (he : ∀ k, P.coeff (PolynomialLinearSolver.exponentAt N d k).val = v[k]) :
    (PolynomialLinearSolver.denotePolynomial N d v).val = P := by
  have heq : PolynomialLinearSolver.denotePolynomial N d v = ⟨P, hP⟩ := by
    apply (EffectiveLinear.boxCoordinates K N d).injective
    funext a
    rw [EffectiveLinear.boxCoordinates_apply, EffectiveLinear.boxCoordinates_apply,
      PolynomialLinearSolver.denotePolynomial_coeff]
    have h := he ((PolynomialLinearSolver.boxIndex N d).symm a)
    have ha := (PolynomialLinearSolver.boxIndex N d).apply_symm_apply a
    change PolynomialLinearSolver.exponentAt N d ((PolynomialLinearSolver.boxIndex N d).symm a) = a at ha
    rw [ha] at h
    exact h.symm
  exact congrArg Subtype.val heq

/-- The executed dense lift is exactly the canonical native polynomial lift. -/
theorem liftDense_correct (d : ℕ) (v : LaurentArithmetic.Dense K D h)
    (hd : 2 * D * h ≤ d) :
    (PolynomialLinearSolver.denotePolynomial (D + D) d (liftDense d v)).val =
      LaurentPresentation.variableEquiv
        (LaurentPresentation.liftPolynomial D K (LaurentArithmetic.denote v)) := by
  apply polynomialDenote_eq_of_coeff
  · apply EffectiveLinear.mem_box_of_totalDegree_le
    rw [LaurentPresentation.variableEquiv_degree]
    exact (LaurentPresentation.liftPolynomial_degree D K _ h
      (LaurentArithmetic.denote_supported v)).trans hd
  · intro k
    simp only [liftDense, Fin.getElem_fin, Vector.getElem_ofFn]
    exact (liftLookup_eq_coeff v _).symm

end Decoupling.HighDim.LaurentLinearSolver
