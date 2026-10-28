import Decoupling.HighDim.EffectiveLinearDescent

/-!
# Degree-preserving descent of homogeneous generator bounds

The extension-field span argument is descended using all coefficient
functionals, including their coefficient-weighted variants. This avoids an
unproved assertion that projecting a generating family remains generating.
This is a field-descent implication; the infinite-field Hermann bound must
still be supplied by the actual elimination proof.
-/

namespace Decoupling.HighDim.EffectiveLinear
open MvPolynomial Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K L : Type*} [CommRing K] [CommRing L] [Algebra K L] {σ : Type*}

def weightedFunctional (f : L →ₗ[K] K) (a : L) : L →ₗ[K] K :=
  f.comp (LinearMap.mulLeft K a)

/-- Coefficient projection of a monomial product uses the weighted functional. -/
theorem projection_monomial_mul (f : L →ₗ[K] K) (a : σ →₀ ℕ) (c : L)
    (Q : MvPolynomial σ L) :
    coefficientProjection f (MvPolynomial.monomial a c * Q) =
      MvPolynomial.monomial a (1 : K) * coefficientProjection (weightedFunctional f c) Q := by
  classical
  ext b
  simp only [coefficientProjection_coeff, MvPolynomial.coeff_monomial_mul', one_mul]
  split <;> simp [weightedFunctional]

/-- An arbitrary extension polynomial scalar splits into base monomials and
weighted coefficient functionals; no multiplicativity of projection is assumed. -/
theorem projection_mul (f : L →ₗ[K] K) (P Q : MvPolynomial σ L) :
    coefficientProjection f (P * Q) =
      ∑ a ∈ P.support, MvPolynomial.monomial a (1 : K) *
        coefficientProjection (weightedFunctional f (P.coeff a)) Q := by
  nth_rw 1 [MvPolynomial.as_sum P]
  rw [Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro a _
  exact projection_monomial_mul f a (P.coeff a) Q

variable {m n N : ℕ}

/-- The actual degree-bounded part of the genuine polynomial kernel. -/
def degreeKernel (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K)) (B : ℕ) :
    Set (Fin n → MvPolynomial (Fin N) K) :=
  {y | A *ᵥ y = 0 ∧ ∀ j, (y j).totalDegree ≤ B}

def projectVector (f : L →ₗ[K] K) (y : Fin n → MvPolynomial (Fin N) L) :=
  fun j => coefficientProjection f (y j)

theorem projectVector_kernel (f : L →ₗ[K] K)
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (y : Fin n → MvPolynomial (Fin N) L)
    (hy : A.map (MvPolynomial.map (algebraMap K L)) *ᵥ y = 0) :
    A *ᵥ projectVector f y = 0 := by
  unfold projectVector
  rw [← coefficientProjection_mulVec, hy]
  funext i
  exact map_zero _

theorem projectVector_degreeKernel (f : L →ₗ[K] K)
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K)) (B : ℕ)
    (y : Fin n → MvPolynomial (Fin N) L)
    (hy : y ∈ degreeKernel (A.map (MvPolynomial.map (algebraMap K L))) B) :
    projectVector f y ∈ degreeKernel A B :=
  ⟨projectVector_kernel f A y hy.1,
    fun j => (coefficientProjection_totalDegree f (y j)).trans (hy.2 j)⟩

/-- Projection preserves membership in the span of all bounded kernel elements.
The scalar step expands the extension polynomial and varies the functional. -/
theorem projection_mem_bounded_kernel_span
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K)) (B : ℕ)
    (y : Fin n → MvPolynomial (Fin N) L)
    (hy : y ∈ Submodule.span (MvPolynomial (Fin N) L)
      (degreeKernel (A.map (MvPolynomial.map (algebraMap K L))) B)) :
    ∀ f : L →ₗ[K] K,
      projectVector f y ∈ Submodule.span (MvPolynomial (Fin N) K) (degreeKernel A B) := by
  classical
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hy
  · intro x hx f
    exact Submodule.subset_span (projectVector_degreeKernel f A B x hx)
  · intro f
    have he : projectVector f (0 : Fin n → MvPolynomial (Fin N) L) = 0 := by
      funext j
      exact map_zero _
    rw [he]
    exact Submodule.zero_mem _
  · intro x z hx hz ihx ihz f
    have he : projectVector f (x + z) = projectVector f x + projectVector f z := by
      funext j
      exact map_add (coefficientProjection f) (x j) (z j)
    rw [he]
    exact Submodule.add_mem _ (ihx f) (ihz f)
  · intro a x hx ihx f
    have he : projectVector f (a • x) =
        ∑ t ∈ a.support, MvPolynomial.monomial t (1 : K) •
          projectVector (weightedFunctional f (a.coeff t)) x := by
      funext j
      simpa only [projectVector, Pi.smul_apply, smul_eq_mul, Finset.sum_apply] using
        projection_mul f a (x j)
    rw [he]
    apply Submodule.sum_mem
    intro t _
    exact Submodule.smul_mem _ _ (ihx _)

section Fields
variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- An actual homogeneous generation bound over an extension implies the same
bound over the original field. This implication is valid also for finite fields. -/
theorem descend_kernel_generation
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) F)) (B : ℕ)
    (hE : LinearMap.ker (A.map (MvPolynomial.map (algebraMap F E))).mulVecLin =
      Submodule.span (MvPolynomial (Fin N) E)
        (degreeKernel (A.map (MvPolynomial.map (algebraMap F E))) B)) :
    LinearMap.ker A.mulVecLin =
      Submodule.span (MvPolynomial (Fin N) F) (degreeKernel A B) := by
  classical
  apply le_antisymm
  · intro y hy
    let z := fun j => MvPolynomial.map (algebraMap F E) (y j)
    have hz : z ∈ Submodule.span (MvPolynomial (Fin N) E)
        (degreeKernel (A.map (MvPolynomial.map (algebraMap F E))) B) := by
      rw [← hE]
      funext i
      exact ((MvPolynomial.map (algebraMap F E)).map_mulVec A y i).symm.trans
        (by rw [show A *ᵥ y = 0 from hy]; simp)
    obtain ⟨f, hf⟩ := exists_coefficient_retraction (F := F) (E := E)
    have hp := projection_mem_bounded_kernel_span A B z hz f
    have he : projectVector f z = y := by
      funext j
      exact coefficientProjection_map f hf (y j)
    rwa [he] at hp
  · exact Submodule.span_le.mpr (fun _ hy => hy.1)

end Fields
end
end Decoupling.HighDim.EffectiveLinear
