import Decoupling.HighDim.AlgorithmTwoPipelineResourceStable
import Decoupling.HighDim.AlgorithmTwoPipelineC4

/-! # Resource bound for the executable array-only C4 stage
The solved cone supplies readiness internally. Equality with the native
execution includes its trace; no native equivalence is executed as data.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipelineResource
open AlgorithmTwoPipeline AlgorithmTwoResourceBudget AlgorithmTwoInputGrowth
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
  (H : StoredHomotopy coords inp hDL out target gamma)
  (x : StoredExtraction coords inp hDL out target gamma H)

theorem stable_program_cost :
    (stableProgram coords inp hDL out target gamma H x).cost ≤
      stable D L (inputBudget (L := L) (h := h) coords) := by
  let : C.IsGE 1 := input_isGE coords inp
  let : (AlgorithmTwoToricData.nativeStack D out.multiplicities K).IsGE 1 :=
    AlgorithmTwoToricData.nativeStack_isGE_one D out.multiplicities K
  let : (AlgorithmTwoToricData.nativeStack D out.multiplicities K).IsStrictlyGE (-(L:ℤ)) :=
    target_lower_bound coords inp hDL out
  rw [stableProgram_eq_execute]
  exact stable_execute_cost coords inp hDL out (nativeArrays coords inp hDL out target gamma H x)
    (computedEquivalence coords inp hDL out target gamma H).symm
    (nativeArrays_realizes coords inp hDL out target gamma H x)

end Decoupling.HighDim.AlgorithmTwoPipelineResource
