import Decoupling.HighDim.AlgorithmTwoBackendCost
import Decoupling.HighDim.AlgorithmTwoPipelineMaterialized

/-!
# HD012 Proposition 1 for the public finite-vector interface

The input size counts the actual stored block dimensions and their common
coefficient box. Shape correctness identifies this literal count with the
native input size. Neither ranks, box headers nor padded matrices are
added to the count.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipelineBackend
variable {K : Type} {D L h : ℕ}

def MaterializedInput.coefficientCount (a : MaterializedInput K D L h) : ℕ :=
  ∑ i : Fin (AlgorithmTwoPipeline.inputLength L),
    (a.blocks.get i).rows*(a.blocks.get i).columns*LaurentArithmetic.boxSize D h

theorem MaterializedInput.toRaw_coefficientCount (a : MaterializedInput K D L h) :
    AlgorithmTwoPipelineBackend.coefficientCount a.toRaw = a.coefficientCount := by
  unfold AlgorithmTwoPipelineBackend.coefficientCount MaterializedInput.coefficientCount
  apply Finset.sum_congr rfl
  intro i _
  rw [(a.shape i).1,(a.shape i).2]
  rfl

variable [Field K] [DecidableEq K]

/-- The actual public execution has one common dimension-dependent
polynomial bound for arithmetic, emitted depth and both ancillary counts. -/
theorem materialized_polynomial_cost (a : MaterializedInput K D (D+2) h)
    (valid : Valid a.toRaw) (hD : 2 ≤ D) :
    let run := executeMaterialized a valid (by omega : D ≤ D+2)
    let B := (AlgorithmTwoResourceBudget.paperPolynomial D).eval a.coefficientCount
    run.cost ≤ B ∧ run.value.gates.length ≤ B ∧ run.value.sourceAncillas ≤ B ∧
      run.value.targetAncillas ≤ B ∧ run.value.species ≤ B := by
  have hr := polynomial_cost a.toRaw valid hD
  rw [a.toRaw_coefficientCount] at hr
  exact hr

end Decoupling.HighDim.AlgorithmTwoPipelineBackend

namespace Decoupling.HighDim.AlgorithmTwoPipelineBackend

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
  refine ⟨AlgorithmTwoResourceBudget.paperPolynomial D,?_⟩
  intro K instK instDec h a valid
  have hr := materialized_polynomial_cost a valid hD
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

end Decoupling.HighDim.AlgorithmTwoPipelineBackend
