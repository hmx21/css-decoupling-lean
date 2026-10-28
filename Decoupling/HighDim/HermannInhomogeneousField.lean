import Decoupling.HighDim.HermannInhomogeneous
import Decoupling.HighDim.EffectiveLinearDescent
import Mathlib.FieldTheory.RatFunc.Basic

/-!
# The unconditional polynomial solution bound over every field

The actual degree theorem over an infinite coefficient field is descended
from K(T) using a constructed K-linear coefficient retraction. The resulting
statement has no infinite-field or extension-field input. The wider bound
(4*m*d)^(2^N) includes all lift/reassembly terms and is sufficient for the
fixed-spatial-dimension polynomial-cost claim.
-/

namespace Decoupling.HighDim.Hermann
open Matrix MvPolynomial
noncomputable section
variable {K : Type*} [Field K] {N m n d : ℕ}

/-- Coefficient extension does not increase the actual total degree. -/
theorem map_totalDegree_le {L : Type*} [CommRing L] (f : K →+* L)
    (P : MvPolynomial (Fin N) K) : (MvPolynomial.map f P).totalDegree ≤ P.totalDegree :=
  Finset.sup_mono (MvPolynomial.support_map_subset f P)

/-- Every solvable actual polynomial system over any field has a solution
within the explicit recursive degree budget. -/
theorem bounded_solution (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (v : Fin m → MvPolynomial (Fin N) K)
    (hA : ∀ i j, (A i j).totalDegree ≤ d) (hv : ∀ i, (v i).totalDegree ≤ d)
    (hsol : ∃ y, A *ᵥ y = v) :
    ∃ y, A *ᵥ y = v ∧ ∀ j, (y j).totalDegree ≤ solutionBound N m d := by
  let L := RatFunc K
  let : Infinite L := Infinite.of_injective (algebraMap (Polynomial K) L) (IsFractionRing.injective _ _)
  let f := MvPolynomial.map (algebraMap K L) (σ := Fin N)
  have hs : ∃ y, A.map f *ᵥ y = f ∘ v := by
    obtain ⟨y, hy⟩ := hsol
    refine ⟨f ∘ y, ?_⟩
    funext i
    exact (f.map_mulVec A y i).symm.trans (congrArg f (congrFun hy i))
  obtain ⟨y, hy, hdeg⟩ := bounded_solution_infinite N m n d (A.map f) (f ∘ v)
    (fun i j => (map_totalDegree_le _ (A i j)).trans (hA i j))
    (fun i => (map_totalDegree_le _ (v i)).trans (hv i)) hs
  exact EffectiveLinear.descend_bounded_solution A v (solutionBound N m d) y hy hdeg

/-- A closed, sufficient fixed-variable degree bound for genuine systems.
The factor 4 is conservative; no claim that it equals the sharp cited constant is made. -/
theorem solution_degree_le (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (v : Fin m → MvPolynomial (Fin N) K)
    (hA : ∀ i j, (A i j).totalDegree ≤ d) (hv : ∀ i, (v i).totalDegree ≤ d)
    (hsol : ∃ y, A *ᵥ y = v) :
    ∃ y, A *ᵥ y = v ∧ ∀ j, (y j).totalDegree ≤ (4 * m * d) ^ (2 ^ N) := by
  obtain ⟨y, hy, hdeg⟩ := bounded_solution A v hA hv hsol
  exact ⟨y, hy, fun j => (hdeg j).trans (solutionBound_le N m d)⟩

end
end Decoupling.HighDim.Hermann
