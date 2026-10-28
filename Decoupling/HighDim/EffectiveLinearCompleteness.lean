import Decoupling.HighDim.HermannInhomogeneousField
import Decoupling.HighDim.EffectiveLinearMatrixEntries

/-!
# An unconditional finite-coefficient solvability criterion

For arbitrary polynomial systems over a field, this file removes the bounded
solution hypothesis from the finite coefficient reduction by using the proved
Hermann elimination bound. Thus the finite system is complete for the original
unbounded polynomial equation, not merely sound for a search window.
-/

namespace Decoupling.HighDim.EffectiveLinear
open Matrix MvPolynomial
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {N m n d : ℕ}

/-- The conservative proved degree cutoff for the actual finite search. -/
def solutionCutoff (N m d : ℕ) : ℕ := (4 * m * d) ^ (2 ^ N)

theorem mem_box_of_totalDegree_le {P : MvPolynomial (Fin N) K} {b : ℕ}
    (h : P.totalDegree ≤ b) : P ∈ MvPolynomial.restrictDegree (Fin N) K b :=
  MvPolynomial.restrictTotalDegree_le_restrictDegree (Fin N) K b
    ((MvPolynomial.mem_restrictTotalDegree _ _ _).mpr h)

def outputBox (v : Fin m → MvPolynomial (Fin N) K)
    (hv : ∀ i, (v i).totalDegree ≤ d) :
    Fin m → BoxPolynomial K N (d + solutionCutoff N m d) :=
  fun i => ⟨v i, mem_box_of_totalDegree_le ((hv i).trans (Nat.le_add_right _ _))⟩

/-- Exact complete coefficient-system criterion using the proved cutoff.
Only the degrees of the supplied coefficients are bounded as input. -/
theorem solvable_iff_coefficient_system
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (v : Fin m → MvPolynomial (Fin N) K)
    (hA : ∀ i j, (A i j).totalDegree ≤ d) (hv : ∀ i, (v i).totalDegree ≤ d) :
    (∃ y, A *ᵥ y = v) ↔
      ∃ z : (Fin n × BoxExponent N (solutionCutoff N m d)) → K,
        coefficientMatrix A (fun i j => mem_box_of_totalDegree_le (hA i j))
          (solutionCutoff N m d) *ᵥ z =
            vectorCoordinates K N m (d + solutionCutoff N m d) (outputBox v hv) := by
  constructor
  · intro hsol
    obtain ⟨y, hy, hdeg⟩ := Hermann.solution_degree_le A v hA hv hsol
    apply (bounded_solution_iff A (fun i j => mem_box_of_totalDegree_le (hA i j))
      (solutionCutoff N m d) (outputBox v hv)).mp
    exact ⟨fun j => ⟨y j, mem_box_of_totalDegree_le (hdeg j)⟩, hy⟩
  · intro hs
    obtain ⟨y, hy⟩ := (bounded_solution_iff A (fun i j => mem_box_of_totalDegree_le (hA i j))
      (solutionCutoff N m d) (outputBox v hv)).mpr hs
    exact ⟨fun j => (y j).val, hy⟩

/-- Explicit finite matrix dimensions for the complete search. -/
theorem complete_matrix_sizes :
    Fintype.card (Fin n × BoxExponent N (solutionCutoff N m d)) =
        n * (solutionCutoff N m d + 1) ^ N ∧
      Fintype.card (Fin m × BoxExponent N (d + solutionCutoff N m d)) =
        m * (d + solutionCutoff N m d + 1) ^ N := by
  simp

end
end Decoupling.HighDim.EffectiveLinear
