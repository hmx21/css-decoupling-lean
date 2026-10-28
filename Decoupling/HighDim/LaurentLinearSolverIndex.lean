import Decoupling.HighDim.LaurentArithmeticData
import Decoupling.HighDim.LaurentIndexedKernel
import Decoupling.HighDim.PolynomialLinearSolverData

/-!
# Computable exponent maps for the Laurent solver

Positive/negative splitting and recombination use only integer/natural-number
operations. The denotation lemmas identify these computable maps with the
actual polynomial presentation; no field-valued oracle is used.
-/

namespace Decoupling.HighDim.LaurentLinearSolver
open Matrix MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Canonical positive/negative exponent split, using explicit finite support. -/
def splitExponent (D : ℕ) (a : Translation D) : Fin (D + D) →₀ ℕ :=
  PolynomialLinearSolver.exponentOfFunction (fun j =>
    Sum.elim (fun i => (a i).toNat) (fun i => (-a i).toNat) (finSumFinEquiv.symm j))

/-- The actual Laurent exponent associated with a doubled-variable monomial. -/
def joinExponent (D : ℕ) (a : Fin (D + D) →₀ ℕ) : Translation D :=
  fun i => (a (finSumFinEquiv (Sum.inl i)) : ℤ) - a (finSumFinEquiv (Sum.inr i))

@[simp] theorem join_split (D : ℕ) (a : Translation D) :
    joinExponent D (splitExponent D a) = a := by
  funext i
  simp only [joinExponent, splitExponent, PolynomialLinearSolver.exponentOfFunction_apply,
    Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr]
  omega

theorem splitExponent_injective (D : ℕ) : Function.Injective (splitExponent D) :=
  fun a b h => by simpa only [join_split] using congrArg (joinExponent D) h

variable {K : Type*} [Field K] {D : ℕ}

theorem variableEquiv_lift_monomial (a : Translation D) (c : K) :
    LaurentPresentation.variableEquiv (MvPolynomial.monomial (LaurentPresentation.liftExponent D a) c) =
      MvPolynomial.monomial (splitExponent D a) c := by
  rw [LaurentPresentation.variableEquiv, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_monomial]
  have he : Finsupp.mapDomain finSumFinEquiv (LaurentPresentation.liftExponent D a) =
      splitExponent D a := by
    ext j
    rw [Finsupp.mapDomain_equiv_apply]
    rfl
  rw [he]

theorem indexedEvaluation_monomial (a : Fin (D + D) →₀ ℕ) (c : K) :
    LaurentPresentation.indexedEvaluation (MvPolynomial.monomial a c) =
      AddMonoidAlgebra.single (joinExponent D a) c := by
  change LaurentPresentation.evaluate K D
    ((MvPolynomial.renameEquiv K finSumFinEquiv).symm (MvPolynomial.monomial a c)) = _
  rw [MvPolynomial.renameEquiv_symm, MvPolynomial.renameEquiv_apply,
    MvPolynomial.rename_monomial, LaurentPresentation.evaluate_monomial]
  congr 1
  funext i
  change ((Finsupp.mapDomain finSumFinEquiv.symm a) (Sum.inl i) : ℤ) -
    (Finsupp.mapDomain finSumFinEquiv.symm a) (Sum.inr i) = _
  rw [Finsupp.mapDomain_equiv_apply, Finsupp.mapDomain_equiv_apply]
  rfl

/-- The semantic polynomial is the actual finite sum of all supplied coefficients. -/
theorem denotePolynomial_eq_sum (N b : ℕ) (v : Vector K (PolynomialLinearSolver.boxSize N b)) :
    (PolynomialLinearSolver.denotePolynomial N b v).val =
      ∑ k, MvPolynomial.monomial (PolynomialLinearSolver.exponentAt N b k).val v[k] := by
  classical
  ext a
  rw [MvPolynomial.coeff_sum]
  by_cases ha : ∀ i, a i ≤ b
  · let a' : EffectiveLinear.BoxExponent N b := ⟨a, ha⟩
    rw [PolynomialLinearSolver.denotePolynomial_coeff N b v a']
    symm
    rw [Finset.sum_eq_single ((PolynomialLinearSolver.boxIndex N b).symm a')]
    · have he := (PolynomialLinearSolver.boxIndex N b).apply_symm_apply a'
      change PolynomialLinearSolver.exponentAt N b ((PolynomialLinearSolver.boxIndex N b).symm a') = a' at he
      rw [he]
      simp [a']
    · intro k _ hk
      have he : (PolynomialLinearSolver.exponentAt N b k).val ≠ a := by
        intro he
        apply hk
        apply (PolynomialLinearSolver.boxIndex N b).injective
        exact (Subtype.ext he).trans ((PolynomialLinearSolver.boxIndex N b).apply_symm_apply a').symm
      simp [MvPolynomial.coeff_monomial, he]
    · simp
  · rw [PolynomialLinearSolver.boxed_coeff_zero _ _ ha]
    symm
    apply Finset.sum_eq_zero
    intro k _
    have he : (PolynomialLinearSolver.exponentAt N b k).val ≠ a := by
      intro he
      exact ha (he ▸ (PolynomialLinearSolver.exponentAt N b k).property)
    simp [MvPolynomial.coeff_monomial, he]

end Decoupling.HighDim.LaurentLinearSolver
