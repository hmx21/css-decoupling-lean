import Decoupling.HighDim.AlgorithmTwoPipelineMaterialized
import Decoupling.HighDim.SequentialPipelineBackend

/- HD016: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of Algorithm 2”.
New sequential-contraction execution; historical AlgorithmTwoPipelineMaterialized is preserved. -/
/-!
# Public finite-vector input boundary

Every input field coefficient is in an actual stored Vector. Shape proofs
only reconcile dependent dimensions; extracting a block performs index
lookup and copying, never unrecorded field arithmetic. RawInput remains a
convenient semantic family of these stored blocks, not the public runtime
coefficient oracle.
-/
namespace Decoupling.HighDim.SequentialBackend
open AlgorithmTwoPipeline AlgorithmTwoPipelineBackend AlgorithmTwo
open SequentialPipeline
open ArithmeticCost LaurentArithmetic
variable {K : Type} {D L h : ℕ}

variable [Field K] [DecidableEq K]

/-- Closed public entry: actual finite data, original complex/profile validity
in Prop, and the original dimension-bound relation. -/
def executeMaterialized (a : MaterializedInput K D L h) (valid : Valid a.toRaw) (hDL : D ≤ L) :
    Work K (AlgorithmTwoPipeline.RuntimeOutput K D) := execute a.toRaw valid hDL

theorem executeMaterialized_eq_program (a : MaterializedInput K D L h) (valid : Valid a.toRaw) (hDL : D ≤ L) :
    executeMaterialized a valid hDL = SequentialAlgorithmTwo.program (coordinates a.toRaw (Classical.choose valid))
      (originalInput a.toRaw (Classical.choose valid) (Classical.choose_spec valid)) hDL :=
  execute_eq_program a.toRaw valid hDL

end Decoupling.HighDim.SequentialBackend
