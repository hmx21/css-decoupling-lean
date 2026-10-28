import Decoupling.HighDim.AlgorithmTwoPipelineResourceGamma
import Decoupling.HighDim.AlgorithmTwoPipelineCone

/-! # Executed cone solve plus signed block extraction in the same budget -/
namespace Decoupling.HighDim.AlgorithmTwoPipelineResource
open AlgorithmTwoPipeline AlgorithmTwoResourceBudget AlgorithmTwoInputGrowth ArithmeticCost
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

theorem homotopy_radius : homotopyRadius coords inp hDL out ≤
    cone D (inputBudget (L := L) (h := h) coords) :=
  homotopy_radius_numeric coords inp hDL out

theorem c4_radius : c4Radius coords inp hDL out ≤ cone D (inputBudget (L := L) (h := h) coords) :=
  c4_radius_numeric coords inp hDL out

theorem cone_program_cost (H : StoredHomotopy coords inp hDL out target gamma) :
    (homotopyProgram coords inp hDL out target gamma).cost +
      (extractionProgram coords inp hDL out target gamma H).cost ≤
      cone D (inputBudget (L := L) (h := h) coords) := by
  rw [extractionProgram_cost, pow_two]
  apply (Nat.add_le_add_right (homotopyProgram_cost coords inp hDL out target gamma) _).trans
  simpa only [pow_two,coneRank,coneRadius,homotopyRadius] using cone_cost_numeric coords inp hDL out

theorem cone_bind_cost :
    (Work.bind (homotopyProgram coords inp hDL out target gamma) fun H =>
      Work.bind (extractionProgram coords inp hDL out target gamma H) fun x =>
        Work.pure (⟨H,x⟩ : Σ H, StoredExtraction coords inp hDL out target gamma H)).cost ≤
      cone D (inputBudget (L := L) (h := h) coords) := by
  simp only [Work.bind_cost, Work.pure_cost, add_zero]
  exact cone_program_cost coords inp hDL out target gamma _

end Decoupling.HighDim.AlgorithmTwoPipelineResource
