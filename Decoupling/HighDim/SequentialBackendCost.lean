import Decoupling.HighDim.SequentialPipelineBackend
import Decoupling.HighDim.AlgorithmTwoBackendCost
import Decoupling.HighDim.SequentialPolynomialCost

/-!
Source: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of
Algorithm 2”. This endpoint runs the new descending-contraction pipeline.

# HD016 Proposition 1 for the closed finite-data execution entry

The runtime arguments are a finite rank vector and the original adjacent
coefficient arrays. Validity is an erased proposition expressing only
the chain equation and original split-profile condition. Equality of the
complete Work object transfers the already proved cost and output bounds.
-/
namespace Decoupling.HighDim.SequentialBackend
open AlgorithmTwoPipeline AlgorithmTwoPipelineBackend
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}

/-- The same polynomial in the exact original input size bounds the
actual finite-data execution, including its true zero branch. -/
theorem polynomial_cost (raw : RawInput K D (D+2) h) (valid : Valid raw) (hD : 2 ≤ D) :
    let run := execute raw valid (by omega : D ≤ D+2)
    let B := (SequentialResourceBudget.paperPolynomial D).eval (coefficientCount raw)
    run.cost ≤ B ∧ run.value.gates.length ≤ B ∧ run.value.sourceAncillas ≤ B ∧
      run.value.targetAncillas ≤ B ∧ run.value.species ≤ B := by
  dsimp only
  rw [execute_eq_program]
  exact SequentialAlgorithmTwo.polynomial_cost
    (coordinates raw (Classical.choose valid))
    (originalInput raw (Classical.choose valid) (Classical.choose_spec valid)) hD

end Decoupling.HighDim.SequentialBackend

namespace Decoupling.HighDim.SequentialBackend
open AlgorithmTwoPipelineBackend

/-- Proposition 1 for finite raw data, with one dimension-dependent
polynomial uniformly over fields and all valid original array inputs. -/
theorem proposition_one (D : ℕ) (hD : 2 ≤ D) :
    ∃ P : Polynomial ℕ,
      ∀ (K : Type) [Field K] [DecidableEq K] (h : ℕ)
        (raw : RawInput K D (D+2) h) (valid : Valid raw),
        let run := execute raw valid (by omega : D ≤ D+2)
        run.cost ≤ P.eval (coefficientCount raw) ∧
          run.value.gates.length ≤ P.eval (coefficientCount raw) ∧
          run.value.sourceAncillas ≤ P.eval (coefficientCount raw) ∧
          run.value.targetAncillas ≤ P.eval (coefficientCount raw) := by
  refine ⟨SequentialResourceBudget.paperPolynomial D,?_⟩
  intro K instK instDec h raw valid
  have hr := polynomial_cost raw valid hD
  exact ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.1⟩

end Decoupling.HighDim.SequentialBackend
