import Decoupling.HighDim.LaurentPresentationSystems
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# HD012 projection of polynomial syzygies generates the exact Laurent kernel

This uses the genuine polynomial presentation and its solution lifting.
The polynomial generator premise is the contract of the polynomial-kernel
routine, not a definition of the Laurent kernel or a global cost assumption.
-/
namespace Decoupling.HighDim.LaurentPresentation
open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [CommRing K] {D m n t : ℕ}
  (A : Matrix (Fin m) (Fin n) (Laurent K D))

def projectMatrix (V : Matrix (Fin n ⊕ (Fin m × Fin D)) (Fin t) (Poly K D)) :
    Matrix (Fin n) (Fin t) (Laurent K D) := fun i j => evaluate K D (V (Sum.inl i) j)

theorem project_mulVec (V : Matrix (Fin n ⊕ (Fin m × Fin D)) (Fin t) (Poly K D))
    (z : Fin t → Poly K D) :
    projectVector (V *ᵥ z) = projectMatrix V *ᵥ (fun j => evaluate K D (z j)) := by
  funext i
  simp [projectVector, projectMatrix, Matrix.mulVec, dotProduct]

/-- Projecting the computed polynomial kernel generators yields all
Laurent syzygies, including those with negative exponents. -/
theorem projected_kernel_generators
    (V : Matrix (Fin n ⊕ (Fin m × Fin D)) (Fin t) (Poly K D))
    (hV : V.mulVecLin.range = (expandedMatrix A).mulVecLin.ker) :
    (projectMatrix V).mulVecLin.range = A.mulVecLin.ker := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    let z : Fin t → Poly K D := fun j => liftPolynomial D K (u j)
    have hz : V *ᵥ z ∈ (expandedMatrix A).mulVecLin.ker := by
      rw [← hV]
      exact ⟨z, rfl⟩
    have hp : projectMatrix V *ᵥ u = projectVector (V *ᵥ z) := by
      rw [project_mulVec]
      congr 1
      funext j
      exact (evaluate_liftPolynomial D K (u j)).symm
    change A *ᵥ (projectMatrix V *ᵥ u) = 0
    rw [hp]
    funext i
    rw [← evaluate_expanded]
    change evaluate K D (((expandedMatrix A).mulVecLin (V *ᵥ z)) i) = 0
    change (expandedMatrix A).mulVecLin (V *ᵥ z) = 0 at hz
    rw [hz, Pi.zero_apply, map_zero]
  · intro hy
    obtain ⟨z, hz, hproj⟩ := lift_solution A 0 y hy
    have hz0 : z ∈ (expandedMatrix A).mulVecLin.ker := by
      change expandedMatrix A *ᵥ z = 0
      rw [hz]
      funext i
      simp [liftVector, liftPolynomial]
    rw [← hV] at hz0
    obtain ⟨u, hu⟩ := hz0
    refine ⟨fun j => evaluate K D (u j), ?_⟩
    change projectMatrix V *ᵥ (fun j => evaluate K D (u j)) = y
    rw [← project_mulVec]
    exact (congrArg projectVector hu).trans hproj

end
end Decoupling.HighDim.LaurentPresentation
