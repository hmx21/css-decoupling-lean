import Decoupling.HighDim.SequentialPipelineResourceStable
import Decoupling.HighDim.SequentialPipelineC4

/-!
HD016: Appendix C4 “Inverting Γ” and C5 “The lines of Algorithm 2”;
all resources refer to the descending contraction in the new execution.
 # Resource bound for the executable array-only C4 stage
The solved cone supplies readiness internally. Equality with the native
execution includes its trace; no native equivalence is executed as data.
-/
namespace Decoupling.HighDim.SequentialPipelineResource
open AlgorithmTwoPipeline SequentialPipeline SequentialResourceBudget AlgorithmTwoInputGrowth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
  (inp : Input (D := D) (L := L) (h := h) coords) (hDL : D ≤ L)
  (out : InputLayers coords inp hDL)
  (target : StoredTarget coords inp hDL out)
  (gamma : StoredGamma coords inp hDL out target)
  (H : SequentialPipeline.StoredHomotopy coords inp hDL out target gamma)
  (x : SequentialPipeline.StoredExtraction coords inp hDL out target gamma H)

theorem stable_program_cost :
    (SequentialPipeline.stableProgram coords inp hDL out target gamma H x).cost ≤
      stable D L (inputBudget (L := L) (h := h) coords) := by
  let : C.IsGE 1 := input_isGE coords inp
  let : (AlgorithmTwoToricData.nativeStack D out.multiplicities K).IsGE 1 :=
    AlgorithmTwoToricData.nativeStack_isGE_one D out.multiplicities K
  let : (AlgorithmTwoToricData.nativeStack D out.multiplicities K).IsStrictlyGE (-(L:ℤ)) :=
    SequentialPipeline.target_lower_bound coords inp hDL out
  rw [SequentialPipeline.stableProgram_eq_execute]
  exact stable_execute_cost coords inp hDL out (SequentialPipeline.nativeArrays coords inp hDL out target gamma H x)
    (SequentialPipeline.computedEquivalence coords inp hDL out target gamma H).symm
    (SequentialPipeline.nativeArrays_realizes coords inp hDL out target gamma H x)

end Decoupling.HighDim.SequentialPipelineResource
