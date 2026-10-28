import Decoupling.HighDim.SequentialPipelineResourceGamma
import Decoupling.HighDim.SequentialPipelineCone

/-!
HD016: Appendix C4 “Inverting Γ” and C5 “The lines of Algorithm 2”;
all resources refer to the descending contraction in the new execution.
 # Executed cone solve plus signed block extraction in the same budget -/
namespace Decoupling.HighDim.SequentialPipelineResource
open AlgorithmTwoPipeline SequentialPipeline SequentialResourceBudget AlgorithmTwoInputGrowth ArithmeticCost
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

theorem homotopy_radius : SequentialPipeline.homotopyRadius coords inp hDL out ≤
    cone D L (inputBudget (L := L) (h := h) coords) :=
  homotopy_radius_numeric coords inp hDL out

theorem c4_radius : SequentialPipeline.c4Radius coords inp hDL out ≤ cone D L (inputBudget (L := L) (h := h) coords) :=
  c4_radius_numeric coords inp hDL out

theorem cone_program_cost (H : SequentialPipeline.StoredHomotopy coords inp hDL out target gamma) :
    (SequentialPipeline.homotopyProgram coords inp hDL out target gamma).cost +
      (SequentialPipeline.extractionProgram coords inp hDL out target gamma H).cost ≤
      cone D L (inputBudget (L := L) (h := h) coords) := by
  rw [SequentialPipeline.extractionProgram_cost, pow_two]
  apply (Nat.add_le_add_right (SequentialPipeline.homotopyProgram_cost coords inp hDL out target gamma) _).trans
  simpa only [pow_two,coneRank,coneRadius,SequentialPipeline.homotopyRadius] using cone_cost_numeric coords inp hDL out

theorem cone_bind_cost :
    (Work.bind (SequentialPipeline.homotopyProgram coords inp hDL out target gamma) fun H =>
      Work.bind (SequentialPipeline.extractionProgram coords inp hDL out target gamma H) fun x =>
        Work.pure (⟨H,x⟩ : Σ H, SequentialPipeline.StoredExtraction coords inp hDL out target gamma H)).cost ≤
      cone D L (inputBudget (L := L) (h := h) coords) := by
  simp only [Work.bind_cost, Work.pure_cost, add_zero]
  exact cone_program_cost coords inp hDL out target gamma _

end Decoupling.HighDim.SequentialPipelineResource
