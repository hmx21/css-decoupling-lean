import Decoupling.HighDim.EffectiveLinearCoordinates
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Degree-preserving descent of actual polynomial solutions along field extensions

Hermann's infinite-field argument can be used for finite fields only after
this descent. A linear coefficient retraction is constructed, not assumed.
The theorem preserves the supplied degree bound exactly. It does not prove
that an extension-field bounded solution exists in the first place.
-/

namespace Decoupling.HighDim.EffectiveLinear

open MvPolynomial Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K L : Type*} [CommRing K] [CommRing L] [Algebra K L]
  {σ : Type*}

/-- Apply an actual K-linear coefficient functional to every coefficient. -/
def coefficientProjection (f : L →ₗ[K] K) : MvPolynomial σ L →ₗ[K] MvPolynomial σ K :=
  (AddMonoidAlgebra.coeffLinearEquiv K).symm.toLinearMap.comp
    ((Finsupp.mapRange.linearMap f).comp (AddMonoidAlgebra.coeffLinearEquiv K).toLinearMap)

@[simp] theorem coefficientProjection_coeff (f : L →ₗ[K] K)
    (P : MvPolynomial σ L) (a : σ →₀ ℕ) :
    (coefficientProjection f P).coeff a = f (P.coeff a) := rfl

/-- Projection cannot introduce a new monomial. -/
theorem coefficientProjection_support (f : L →ₗ[K] K) (P : MvPolynomial σ L) :
    (coefficientProjection f P).support ⊆ P.support := by
  intro a ha
  rw [MvPolynomial.mem_support_iff] at ha ⊢
  intro hz
  apply ha
  simp [hz]

/-- In particular the true total degree does not increase. -/
theorem coefficientProjection_totalDegree (f : L →ₗ[K] K) (P : MvPolynomial σ L) :
    (coefficientProjection f P).totalDegree ≤ P.totalDegree :=
  Finset.sup_mono (coefficientProjection_support f P)

/-- Multiplication by a polynomial over the base field commutes with projection. -/
theorem coefficientProjection_map_mul (f : L →ₗ[K] K)
    (P : MvPolynomial σ K) (Q : MvPolynomial σ L) :
    coefficientProjection f (MvPolynomial.map (algebraMap K L) P * Q) =
      P * coefficientProjection f Q := by
  classical
  ext a
  simp only [coefficientProjection_coeff, MvPolynomial.coeff_mul, map_sum,
    MvPolynomial.coeff_map]
  apply Finset.sum_congr rfl
  intro b _
  simpa [Algebra.smul_def] using f.map_smul (P.coeff b.1) (Q.coeff b.2)

/-- A coefficient retraction fixes the entire base polynomial ring. -/
theorem coefficientProjection_map (f : L →ₗ[K] K) (hf : f 1 = 1)
    (P : MvPolynomial σ K) :
    coefficientProjection f (MvPolynomial.map (algebraMap K L) P) = P := by
  ext a
  rw [coefficientProjection_coeff, MvPolynomial.coeff_map]
  have h := f.map_smul (P.coeff a) (1 : L)
  simpa [Algebra.smul_def, hf] using h

/-- Exact compatibility with polynomial matrix multiplication. -/
theorem coefficientProjection_mulVec {m n : ℕ}
    (f : L →ₗ[K] K) (A : Matrix (Fin m) (Fin n) (MvPolynomial σ K))
    (y : Fin n → MvPolynomial σ L) :
    (fun i => coefficientProjection f
      ((A.map (MvPolynomial.map (algebraMap K L)) *ᵥ y) i)) =
      A *ᵥ (fun j => coefficientProjection f (y j)) := by
  funext i
  change coefficientProjection f (∑ j, MvPolynomial.map (algebraMap K L) (A i j) * y j) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact coefficientProjection_map_mul f (A i j) (y j)

section Fields

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- A field extension has a base-linear coefficient retraction normalized at one. -/
theorem exists_coefficient_retraction : ∃ f : E →ₗ[F] F, f 1 = 1 :=
  Module.Projective.exists_dual_eq_one F (one_ne_zero : (1 : E) ≠ 0)

/-- If an actual polynomial system acquires a bounded solution after extending
the coefficient field, a solution of exactly the same bound exists over the base.
There is no separability, infinitude, or finite-extension-degree hypothesis. -/
theorem descend_bounded_solution {m n N : ℕ}
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) F))
    (v : Fin m → MvPolynomial (Fin N) F) (B : ℕ)
    (y : Fin n → MvPolynomial (Fin N) E)
    (hy : A.map (MvPolynomial.map (algebraMap F E)) *ᵥ y =
      fun i => MvPolynomial.map (algebraMap F E) (v i))
    (hdeg : ∀ j, (y j).totalDegree ≤ B) :
    ∃ z : Fin n → MvPolynomial (Fin N) F, A *ᵥ z = v ∧
      ∀ j, (z j).totalDegree ≤ B := by
  obtain ⟨f, hf⟩ := exists_coefficient_retraction (F := F) (E := E)
  refine ⟨fun j => coefficientProjection f (y j), ?_, fun j =>
    (coefficientProjection_totalDegree f (y j)).trans (hdeg j)⟩
  rw [← coefficientProjection_mulVec, hy]
  funext i
  exact coefficientProjection_map f hf (v i)

end Fields
end
end Decoupling.HighDim.EffectiveLinear
