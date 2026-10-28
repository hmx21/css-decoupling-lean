import Decoupling.HighDim.LaurentIndexedSystem
import Decoupling.HighDim.HermannInhomogeneousField

/-!
# HD012 unconditional bounded solutions for actual Laurent systems

The only solvability input is the original Laurent equation. Its bounded
solution is derived by the proved polynomial presentation, the proved
Hermann theorem over arbitrary fields, and evaluation back to Laurent
polynomials. There is no bound, characteristic restriction, infinite-field
hypothesis, or solver oracle in the statement.
-/
namespace Decoupling.HighDim.LaurentPresentation
open Matrix MvPolynomial
noncomputable section
variable {K : Type*} [Field K] {D m n : ℕ}

def solutionBox (D m h : ℕ) : ℕ :=
  (4 * m * max (2 * D * h) 2) ^ (2 ^ (D + D))

/-- A sufficiently large coefficient box for every solvable Laurent system. -/
theorem bounded_laurent_solution (A : Matrix (Fin m) (Fin n) (Laurent K D))
    (b : Fin m → Laurent K D) (h : ℕ)
    (hA : LaurentBoxes.MatrixSupported A h)
    (hb : ∀ i, LaurentBoxes.Supported (b i) h)
    (hsol : ∃ y, A *ᵥ y = b) :
    ∃ y, A *ᵥ y = b ∧ ∀ j, LaurentBoxes.Supported (y j) (solutionBox D m h) := by
  obtain ⟨z, hz, hdeg⟩ := Hermann.solution_degree_le (indexedMatrix A) (indexedRhs b)
    (indexedMatrix_degree A h hA) (indexedRhs_degree b h hb)
    ((indexed_solvable_iff A b).mp hsol)
  refine ⟨projectVector (decodeUnknown z), ?_, ?_⟩
  · have hs := (indexed_solution_iff A b z).mp hz
    funext i
    rw [← evaluate_expanded, hs]
    exact evaluate_liftPolynomial D K (b i)
  · intro j
    apply evaluate_supported
    change (variableEquiv.symm (z (unknownEquiv (Sum.inl j)))).totalDegree ≤ _
    rw [variableEquiv_symm_degree]
    exact hdeg _

end
end Decoupling.HighDim.LaurentPresentation
