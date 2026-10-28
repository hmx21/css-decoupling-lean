import Decoupling.HighDim.AlgorithmTwoMaterializedCost
import Decoupling.HighDim.SequentialBackendCost
import Decoupling.HighDim.SequentialPipelineMaterialized

/-!
Source: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of
Algorithm 2”. This endpoint runs the new descending-contraction pipeline.

# HD016 Proposition 1 for the public finite-vector interface

The input size counts the actual stored block dimensions and their common
coefficient box. Shape correctness identifies this literal count with the
native input size. Neither ranks, box headers nor padded matrices are
added to the count.
-/
namespace Decoupling.HighDim.SequentialBackend
open AlgorithmTwoPipelineBackend
variable {K : Type} {D L h : ℕ}

variable [Field K] [DecidableEq K]

/-- The actual public execution has one common dimension-dependent
polynomial bound for arithmetic, emitted depth and both ancillary counts. -/
theorem materialized_polynomial_cost (a : MaterializedInput K D (D+2) h)
    (valid : Valid a.toRaw) (hD : 2 ≤ D) :
    let run := executeMaterialized a valid (by omega : D ≤ D+2)
    let B := (SequentialResourceBudget.paperPolynomial D).eval a.coefficientCount
    run.cost ≤ B ∧ run.value.gates.length ≤ B ∧ run.value.sourceAncillas ≤ B ∧
      run.value.targetAncillas ≤ B ∧ run.value.species ≤ B := by
  have hr := polynomial_cost a.toRaw valid hD
  rw [a.toRaw_coefficientCount] at hr
  exact hr

end Decoupling.HighDim.SequentialBackend

namespace Decoupling.HighDim.SequentialBackend
open AlgorithmTwoPipelineBackend

/-- Proposition 1 at the public interface. All coefficients and dimensions
are materialized finite vectors; all other input conditions are propositions.
The chosen polynomial is uniform over fields and actual input values. -/
theorem proposition_one_materialized (D : ℕ) (hD : 2 ≤ D) :
    ∃ P : Polynomial ℕ,
      ∀ (K : Type) [Field K] [DecidableEq K] (h : ℕ)
        (a : MaterializedInput K D (D+2) h) (valid : Valid a.toRaw),
        let run := executeMaterialized a valid (by omega : D ≤ D+2)
        run.cost ≤ P.eval a.coefficientCount ∧
          run.value.gates.length ≤ P.eval a.coefficientCount ∧
          run.value.sourceAncillas ≤ P.eval a.coefficientCount ∧
          run.value.targetAncillas ≤ P.eval a.coefficientCount := by
  refine ⟨SequentialResourceBudget.paperPolynomial D,?_⟩
  intro K instK instDec h a valid
  have hr := materialized_polynomial_cost a valid hD
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

end Decoupling.HighDim.SequentialBackend
