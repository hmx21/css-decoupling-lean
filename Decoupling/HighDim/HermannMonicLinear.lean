import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Degree-preserving invertible linear variable changes

HD012 effective Hermann reduction. The first variable is the variable
selected by `MvPolynomial.finSuccEquiv`. All substitutions are displayed
linear forms and the inverse is proved by composition on the variables.
-/

namespace Decoupling.HighDim.Hermann

open MvPolynomial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {N : ℕ}

/-- Evaluation at linear polynomials cannot increase total degree. -/
theorem totalDegree_aeval_linear_le {σ τ : Type*}
    (f : σ → MvPolynomial τ K) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (P : MvPolynomial σ K) : (aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [aeval_monomial]
  change (C (P.coeff d) * ∏ i ∈ d.support, f i ^ d i).totalDegree ≤ P.totalDegree
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply (totalDegree_finsetProd _ _).trans
  calc
    ∑ i ∈ d.support, (f i ^ d i).totalDegree ≤ ∑ i ∈ d.support, d i := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalDegree_pow (f i) (d i)).trans (by simpa using Nat.mul_le_mul_left (d i) (hf i))
    _ ≤ P.totalDegree := le_totalDegree hd

def forwardForm (v : Fin (N+1) → K) : Fin (N+1) → MvPolynomial (Fin (N+1)) K :=
  Fin.cases (C (v 0) * X 0) (fun i => X i.succ + C (v i.succ) * X 0)

def inverseForm (v : Fin (N+1) → K) : Fin (N+1) → MvPolynomial (Fin (N+1)) K :=
  Fin.cases (C ((v 0)⁻¹) * X 0)
    (fun i => X i.succ - C (v i.succ / v 0) * X 0)

def forwardSubstitution (v : Fin (N+1) → K) :
    MvPolynomial (Fin (N+1)) K →ₐ[K] MvPolynomial (Fin (N+1)) K := aeval (forwardForm v)
def inverseSubstitution (v : Fin (N+1) → K) :
    MvPolynomial (Fin (N+1)) K →ₐ[K] MvPolynomial (Fin (N+1)) K := aeval (inverseForm v)

theorem forward_inverse (v : Fin (N+1) → K) (hv : v 0 ≠ 0) :
    (forwardSubstitution v).comp (inverseSubstitution v) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [AlgHom.comp_apply, inverseSubstitution, forwardSubstitution,
      aeval_X, inverseForm, forwardForm, Fin.cases_zero, map_mul, aeval_C,
      MvPolynomial.algebraMap_eq, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ hv, map_one, one_mul]
  · simp only [AlgHom.comp_apply, inverseSubstitution, forwardSubstitution,
      aeval_X, inverseForm, forwardForm, Fin.cases_succ, map_sub, map_mul, aeval_C,
      Fin.cases_zero, MvPolynomial.algebraMap_eq, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul, div_mul_cancel₀ _ hv]
    ring

theorem inverse_forward (v : Fin (N+1) → K) (hv : v 0 ≠ 0) :
    (inverseSubstitution v).comp (forwardSubstitution v) = AlgHom.id K _ := by
  apply MvPolynomial.algHom_ext
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [AlgHom.comp_apply, inverseSubstitution, forwardSubstitution,
      aeval_X, inverseForm, forwardForm, Fin.cases_zero, map_mul, aeval_C,
      MvPolynomial.algebraMap_eq, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul, mul_inv_cancel₀ hv, map_one, one_mul]
  · simp only [AlgHom.comp_apply, inverseSubstitution, forwardSubstitution,
      aeval_X, inverseForm, forwardForm, Fin.cases_succ, map_add, map_mul, aeval_C,
      Fin.cases_zero, MvPolynomial.algebraMap_eq, AlgHom.id_apply]
    rw [← mul_assoc, ← map_mul, ← div_eq_mul_inv]
    ring

/-- An actual algebra automorphism, not an assumed generic coordinate change. -/
def linearCoordinates (v : Fin (N+1) → K) (hv : v 0 ≠ 0) :
    MvPolynomial (Fin (N+1)) K ≃ₐ[K] MvPolynomial (Fin (N+1)) K :=
  AlgEquiv.ofAlgHom (forwardSubstitution v) (inverseSubstitution v)
    (forward_inverse v hv) (inverse_forward v hv)

theorem forwardForm_degree (v : Fin (N+1) → K) (i : Fin (N+1)) :
    (forwardForm v i).totalDegree ≤ 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (totalDegree_mul _ _).trans (by simp)
  · apply (totalDegree_add _ _).trans
    apply max_le
    · simp
    · exact (totalDegree_mul _ _).trans (by simp)

theorem inverseForm_degree (v : Fin (N+1) → K) (i : Fin (N+1)) :
    (inverseForm v i).totalDegree ≤ 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (totalDegree_mul _ _).trans (by simp)
  · apply (totalDegree_sub _ _).trans
    apply max_le
    · simp
    · exact (totalDegree_mul _ _).trans (by simp)

/-- Both linear substitutions have degree at most one, hence the actual
inverse proves equality of total degrees for every polynomial. -/
theorem linearCoordinates_totalDegree (v : Fin (N+1) → K) (hv : v 0 ≠ 0)
    (P : MvPolynomial (Fin (N+1)) K) :
    (linearCoordinates v hv P).totalDegree = P.totalDegree := by
  refine le_antisymm ?_ ?_
  · exact totalDegree_aeval_linear_le _ (forwardForm_degree v) P
  · have h := totalDegree_aeval_linear_le _ (inverseForm_degree v) (linearCoordinates v hv P)
    change ((linearCoordinates v hv).symm (linearCoordinates v hv P)).totalDegree ≤ _ at h
    rw [AlgEquiv.symm_apply_apply] at h
    exact h

end
end Decoupling.HighDim.Hermann
