import Decoupling.HighDim.OnSiteSwap
import Decoupling.HighDim.AlgorithmTwoBackendCorrectness

/-! # The actual public output contains at most one on-site SWAP per species -/
namespace Decoupling.HighDim.OnSiteSwap
open ArithmeticCost AlgorithmTwoPipeline AlgorithmTwoPipelineBackend SparseCircuit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
  (inp : Input (D := D) (L := L) (h := h) coords) (hDL : D ≤ L)

theorem finish_swaps (q : Stages coords inp hDL) :
    swapCount (finishProgram coords inp hDL q).value.gates ≤
      (finishProgram coords inp hDL q).value.species :=
  canonical_count_le _ _

theorem materialized_swaps (a : MaterializedInput K D L h) (valid : Valid a.toRaw) :
    swapCount (executeMaterialized a valid hDL).value.gates ≤
      (executeMaterialized a valid hDL).value.species := by
  change swapCount (execute a.toRaw valid hDL).value.gates ≤
    (execute a.toRaw valid hDL).value.species
  by_cases hz : storedRank a.toRaw = 0
  · rw [execute_zero a.toRaw valid hDL hz]
    exact Nat.le_refl 0
  · rw [execute_nonzero a.toRaw valid hDL hz]
    exact finish_swaps (modelCoordinates a.toRaw valid)
      ((modelInput a.toRaw valid).toPipeline (modelCoordinates a.toRaw valid)) hDL
      (stagesProgram (modelCoordinates a.toRaw valid)
        ((modelInput a.toRaw valid).toPipeline (modelCoordinates a.toRaw valid)) hDL).value

end Decoupling.HighDim.OnSiteSwap
