import Decoupling.HighDim.OnSiteSwap
import Decoupling.HighDim.SequentialBackendCorrectness

/- HD016: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of Algorithm 2”.
New sequential-contraction execution; historical OnSiteSwapPipeline is preserved. -/
/-! # The actual public output contains at most one on-site SWAP per species -/
namespace Decoupling.HighDim.SequentialOnSiteSwap
open AlgorithmTwoPipeline AlgorithmTwoPipelineBackend AlgorithmTwo
open SequentialPipeline
open SequentialBackend
open OnSiteSwap
open ArithmeticCost AlgorithmTwoPipeline AlgorithmTwoPipelineBackend SparseCircuit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
  (inp : Input (D := D) (L := L) (h := h) coords) (hDL : D ≤ L)

theorem finish_swaps (q : SequentialPipeline.Stages coords inp hDL) :
    swapCount (SequentialPipeline.finishProgram coords inp hDL q).value.gates ≤
      (SequentialPipeline.finishProgram coords inp hDL q).value.species :=
  canonical_count_le _ _

theorem materialized_swaps (a : MaterializedInput K D L h) (valid : Valid a.toRaw) :
    swapCount (SequentialBackend.executeMaterialized a valid hDL).value.gates ≤
      (SequentialBackend.executeMaterialized a valid hDL).value.species := by
  change swapCount (SequentialBackend.execute a.toRaw valid hDL).value.gates ≤
    (SequentialBackend.execute a.toRaw valid hDL).value.species
  by_cases hz : storedRank a.toRaw = 0
  · rw [SequentialBackend.execute_zero a.toRaw valid hDL hz]
    exact Nat.le_refl 0
  · rw [SequentialBackend.execute_nonzero a.toRaw valid hDL hz]
    exact finish_swaps (modelCoordinates a.toRaw valid)
      ((modelInput a.toRaw valid).toPipeline (modelCoordinates a.toRaw valid)) hDL
      (SequentialPipeline.stagesProgram (modelCoordinates a.toRaw valid)
        ((modelInput a.toRaw valid).toPipeline (modelCoordinates a.toRaw valid)) hDL).value

end Decoupling.HighDim.SequentialOnSiteSwap
