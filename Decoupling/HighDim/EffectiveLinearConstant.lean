import Decoupling.HighDim.EffectiveLinearKernelDescent
import Mathlib.Algebra.MvPolynomial.Equiv

/-!
# The actual degree-zero base case of effective polynomial linear algebra

For a constant polynomial matrix, each monomial coefficient of an actual
kernel vector is a constant kernel vector. Expanding the original vector
proves generation in degree zero. A constant right-hand side is solved by
taking the actual constant coefficients of any solution. No generator or
solver certificate is assumed, and the proof works over every commutative ring.
-/

namespace Decoupling.HighDim.EffectiveLinear

open MvPolynomial Matrix
noncomputable section
variable {K : Type*} [CommRing K] {N m n : ℕ}

/-- The actual coefficient matrix over the coefficient ring. -/
def constantMatrix (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K)) :
    Matrix (Fin m) (Fin n) K := fun i j => (A i j).coeff 0

def coefficientVector (a : Fin N →₀ ℕ) (y : Fin n → MvPolynomial (Fin N) K) :
    Fin n → K := fun j => (y j).coeff a

def constantVector (x : Fin n → K) : Fin n → MvPolynomial (Fin N) K :=
  fun j => C (x j)

theorem constant_entry (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (hA : ∀ i j, (A i j).totalDegree ≤ 0) (i : Fin m) (j : Fin n) :
    A i j = C (constantMatrix A i j) :=
  totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero (hA i j))

/-- Coefficient extraction commutes with the actual constant matrix action. -/
theorem coefficient_mulVec_constant
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (hA : ∀ i j, (A i j).totalDegree ≤ 0)
    (a : Fin N →₀ ℕ) (y : Fin n → MvPolynomial (Fin N) K) :
    coefficientVector a (A *ᵥ y) = constantMatrix A *ᵥ coefficientVector a y := by
  classical
  funext i
  change (∑ j, A i j * y j).coeff a = ∑ j, constantMatrix A i j * (y j).coeff a
  rw [coeff_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [constant_entry A hA i j, coeff_C_mul]

/-- Constant inclusion also commutes with the actual matrix action. -/
theorem constantVector_mulVec
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (hA : ∀ i j, (A i j).totalDegree ≤ 0) (x : Fin n → K) :
    A *ᵥ constantVector x = constantVector (constantMatrix A *ᵥ x) := by
  classical
  funext i
  change (∑ j, A i j * C (x j)) = C (∑ j, constantMatrix A i j * x j)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [constant_entry A hA i j, map_mul]

/-- Every monomial coefficient of a genuine kernel vector gives a genuine
constant kernel vector of total degree zero. -/
theorem coefficient_constant_mem_degreeKernel
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (hA : ∀ i j, (A i j).totalDegree ≤ 0)
    (y : Fin n → MvPolynomial (Fin N) K) (hy : A *ᵥ y = 0) (a : Fin N →₀ ℕ) :
    constantVector (coefficientVector a y) ∈ degreeKernel A 0 := by
  constructor
  · rw [constantVector_mulVec A hA, ← coefficient_mulVec_constant A hA, hy]
    funext i
    simp [constantVector, coefficientVector]
  · intro j
    simp [constantVector]

/-- The finite union of all actual component supports. -/
def vectorSupport (y : Fin n → MvPolynomial (Fin N) K) : Finset (Fin N →₀ ℕ) :=
  Finset.univ.biUnion (fun j => (y j).support)

/-- Exact reconstruction, using monomials times the constant coefficient vectors. -/
theorem vector_sum_coefficients (y : Fin n → MvPolynomial (Fin N) K) :
    ∑ a ∈ vectorSupport y, monomial a (1 : K) •
      constantVector (coefficientVector a y) = y := by
  classical
  funext j
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, constantVector, coefficientVector]
  simp_rw [mul_comm (monomial _ (1 : K)), C_mul_monomial, mul_one]
  calc
    _ = ∑ a ∈ (y j).support, monomial a ((y j).coeff a) := by
      symm
      apply Finset.sum_subset
      · intro a ha
        exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, ha⟩
      · intro a _ ha
        have hz : (y j).coeff a = 0 := by
          simpa only [mem_support_iff, not_not] using ha
        simp [hz]
    _ = y j := support_sum_monomial_coeff _

/-- The degree-zero Hermann kernel bound is proved for the actual kernel,
without a supplied generating family. -/
theorem constant_kernel_eq_span
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (hA : ∀ i j, (A i j).totalDegree ≤ 0) :
    LinearMap.ker A.mulVecLin =
      Submodule.span (MvPolynomial (Fin N) K) (degreeKernel A 0) := by
  classical
  apply le_antisymm
  · intro y hy
    rw [← vector_sum_coefficients y]
    apply Submodule.sum_mem
    intro a _
    apply Submodule.smul_mem
    exact Submodule.subset_span (coefficient_constant_mem_degreeKernel A hA y hy a)
  · exact Submodule.span_le.mpr (fun _ hy => hy.1)

/-- The actual constant-coefficient projection of a solution solves a constant
right-hand side. This is a formula, not only an existential assertion. -/
theorem constant_solution_projection
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (hA : ∀ i j, (A i j).totalDegree ≤ 0)
    (b : Fin m → MvPolynomial (Fin N) K) (hb : ∀ i, (b i).totalDegree ≤ 0)
    (y : Fin n → MvPolynomial (Fin N) K) (hy : A *ᵥ y = b) :
    A *ᵥ constantVector (coefficientVector 0 y) = b := by
  rw [constantVector_mulVec A hA, ← coefficient_mulVec_constant A hA, hy]
  funext i
  exact (totalDegree_eq_zero_iff_eq_C.mp (Nat.eq_zero_of_le_zero (hb i))).symm

/-- Solvability of a constant system gives a solution with degree exactly
bounded by zero, over an arbitrary coefficient field or commutative ring. -/
theorem constant_bounded_solution
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (hA : ∀ i j, (A i j).totalDegree ≤ 0)
    (b : Fin m → MvPolynomial (Fin N) K) (hb : ∀ i, (b i).totalDegree ≤ 0)
    (hsol : ∃ y, A *ᵥ y = b) :
    ∃ y, A *ᵥ y = b ∧ ∀ j, (y j).totalDegree ≤ 0 := by
  obtain ⟨y,hy⟩ := hsol
  refine ⟨constantVector (coefficientVector 0 y),
    constant_solution_projection A hA b hb y hy, ?_⟩
  intro j
  simp [constantVector]

/-- With no variables every actual polynomial is constant. -/
theorem noVariables_totalDegree (P : MvPolynomial (Fin 0) K) : P.totalDegree = 0 := by
  have h : C (isEmptyAlgEquiv K (Fin 0) P) = P :=
    (isEmptyAlgEquiv K (Fin 0)).symm_apply_apply P
  rw [← h, totalDegree_C]

/-- The zero-variable endpoint of Hermann induction needs no matrix-degree premise. -/
theorem noVariables_kernel_eq_span
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin 0) K)) :
    LinearMap.ker A.mulVecLin =
      Submodule.span (MvPolynomial (Fin 0) K) (degreeKernel A 0) :=
  constant_kernel_eq_span A (fun i j => (noVariables_totalDegree (A i j)).le)

/-- The zero-variable inhomogeneous endpoint. -/
theorem noVariables_bounded_solution
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin 0) K))
    (b : Fin m → MvPolynomial (Fin 0) K) (hsol : ∃ y, A *ᵥ y = b) :
    ∃ y, A *ᵥ y = b ∧ ∀ j, (y j).totalDegree ≤ 0 :=
  constant_bounded_solution A (fun i j => (noVariables_totalDegree (A i j)).le)
    b (fun i => (noVariables_totalDegree (b i)).le) hsol

end
end Decoupling.HighDim.EffectiveLinear
