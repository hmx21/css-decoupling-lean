import Decoupling.HighDim.SequentialPipelineCostStages
import Decoupling.HighDim.SequentialPipelineResourceStored
import Decoupling.HighDim.SequentialPipelineResourcePhysical
import Decoupling.HighDim.SequentialPipelineProgram

/-!
HD016: Appendix C4 “Inverting Γ” and C5 “The lines of Algorithm 2”;
all resources refer to the descending contraction in the new execution.

# Polynomial resources of the same complete executable Algorithm 2

This closes the trace composition: every stage is evaluated by the real
program, with its stored outputs shared by the next stage. No map,
homotopy, stable isomorphism, solver certificate, intermediate size bound,
or polynomial-cost certificate is a caller-supplied premise.
-/
namespace Decoupling.HighDim.SequentialPipelineResource
open AlgorithmTwoPipeline SequentialPipeline SequentialResourceBudget AlgorithmTwoInputGrowth ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
  (inp : Input (D := D) (L := L) (h := h) coords) (hDL : D ≤ L)

theorem stages_cost_decomposition :
    let q := (SequentialPipeline.stagesProgram coords inp hDL).value
    (SequentialPipeline.stagesProgram coords inp hDL).cost =
      (computeLayers coords inp hDL).cost+(storeTargetProgram coords inp hDL q.layers).cost+
      (gammaProgram coords inp hDL q.layers q.target).cost+
      (SequentialPipeline.homotopyProgram coords inp hDL q.layers q.target q.gamma).cost+
      (SequentialPipeline.extractionProgram coords inp hDL q.layers q.target q.gamma q.homotopy).cost+
      (SequentialPipeline.storeStableProgram coords inp hDL q.layers q.target q.gamma q.homotopy q.extraction).cost := by
  simp only [SequentialPipeline.stagesProgram, Work.bind_cost, Work.pure_cost, Work.bind_value, Work.pure_value]
  omega

theorem stages_cost : (SequentialPipeline.stagesProgram coords inp hDL).cost ≤
    1+layer D (inputBudget (L := L) (h := h) coords)+comparison D (inputBudget (L := L) (h := h) coords)+
      cone D L (inputBudget (L := L) (h := h) coords)+stable D L (inputBudget (L := L) (h := h) coords) := by
  let q := (SequentialPipeline.stagesProgram coords inp hDL).value
  have hp := prefix_cost coords inp hDL q.layers q.target q.gamma q.homotopy
  have hs := stored_stable_cost coords inp hDL q.layers q.target q.gamma q.homotopy q.extraction
  rw [stages_cost_decomposition]
  exact Nat.add_le_add hp hs

theorem finish_cost (q : SequentialPipeline.Stages coords inp hDL) :
    (SequentialPipeline.finishProgram coords inp hDL q).cost ≤ lift D L (inputBudget (L := L) (h := h) coords) := by
  rw [SequentialPipeline.finishProgram_cost]
  have hh := stored_lift_theta_cost coords inp hDL q.layers q.target q.gamma q.homotopy q.extraction q.stable
  rw [Work.bind_cost] at hh
  exact hh

theorem nonzero_cost : (SequentialPipeline.nonzeroProgram coords inp hDL).cost ≤ bound D L (inputBudget (L := L) (h := h) coords) := by
  rw [SequentialPipeline.nonzeroProgram_cost, bound_eq]
  have hs := stages_cost coords inp hDL
  have hf := finish_cost coords inp hDL (SequentialPipeline.stagesProgram coords inp hDL).value
  omega

theorem finish_depth (q : SequentialPipeline.Stages coords inp hDL) :
    (SequentialPipeline.finishProgram coords inp hDL q).value.gates.length ≤ bound D L (inputBudget (L := L) (h := h) coords) :=
  (stored_lift_theta_depth coords inp hDL q.layers q.target q.gamma q.homotopy q.extraction q.stable).trans
    (lift_le_bound D L _)

theorem finish_source_ancillas (q : SequentialPipeline.Stages coords inp hDL) :
    (SequentialPipeline.finishProgram coords inp hDL q).value.sourceAncillas ≤ bound D L (inputBudget (L := L) (h := h) coords) :=
  (source_ancilla_count coords inp hDL q.layers
    (SequentialPipeline.nativeArrays coords inp hDL q.layers q.target q.gamma q.homotopy q.extraction)).trans (lift_le_bound D L _)

theorem finish_target_ancillas (q : SequentialPipeline.Stages coords inp hDL) :
    (SequentialPipeline.finishProgram coords inp hDL q).value.targetAncillas ≤ bound D L (inputBudget (L := L) (h := h) coords) :=
  (target_ancilla_count coords inp hDL q.layers
    (SequentialPipeline.nativeArrays coords inp hDL q.layers q.target q.gamma q.homotopy q.extraction)).trans (lift_le_bound D L _)

theorem finish_species (q : SequentialPipeline.Stages coords inp hDL) :
    (SequentialPipeline.finishProgram coords inp hDL q).value.species ≤ bound D L (inputBudget (L := L) (h := h) coords) :=
  (physical_width coords inp hDL q.layers
    (SequentialPipeline.nativeArrays coords inp hDL q.layers q.target q.gamma q.homotopy q.extraction)).trans (lift_le_bound D L _)

theorem nonzero_depth : (SequentialPipeline.nonzeroProgram coords inp hDL).value.gates.length ≤
    bound D L (inputBudget (L := L) (h := h) coords) :=
  finish_depth coords inp hDL (SequentialPipeline.stagesProgram coords inp hDL).value

theorem nonzero_source_ancillas : (SequentialPipeline.nonzeroProgram coords inp hDL).value.sourceAncillas ≤
    bound D L (inputBudget (L := L) (h := h) coords) :=
  finish_source_ancillas coords inp hDL (SequentialPipeline.stagesProgram coords inp hDL).value

theorem nonzero_target_ancillas : (SequentialPipeline.nonzeroProgram coords inp hDL).value.targetAncillas ≤
    bound D L (inputBudget (L := L) (h := h) coords) :=
  finish_target_ancillas coords inp hDL (SequentialPipeline.stagesProgram coords inp hDL).value

theorem nonzero_species : (SequentialPipeline.nonzeroProgram coords inp hDL).value.species ≤
    bound D L (inputBudget (L := L) (h := h) coords) :=
  finish_species coords inp hDL (SequentialPipeline.stagesProgram coords inp hDL).value

/-- One common polynomial bounds the actual complete trace, the returned
SUM/SWAP depth, both actual added-qudit counts, and physical width. -/
theorem nonzero_resources :
    let run := SequentialPipeline.nonzeroProgram coords inp hDL
    let B := (SequentialResourceBudget.polynomial D L).eval (inputBudget (L := L) (h := h) coords)
    run.cost ≤ B ∧ run.value.gates.length ≤ B ∧ run.value.sourceAncillas ≤ B ∧
      run.value.targetAncillas ≤ B ∧ run.value.species ≤ B :=
  ⟨nonzero_cost coords inp hDL,nonzero_depth coords inp hDL,nonzero_source_ancillas coords inp hDL,
    nonzero_target_ancillas coords inp hDL,nonzero_species coords inp hDL⟩

theorem nonzeroProgram_cost_bound : (SequentialPipeline.nonzeroProgram coords inp hDL).cost ≤
    bound D L (inputBudget (L := L) (h := h) coords) := nonzero_cost coords inp hDL

theorem nonzeroProgram_depth_bound : (SequentialPipeline.nonzeroProgram coords inp hDL).value.gates.length ≤
    bound D L (inputBudget (L := L) (h := h) coords) := nonzero_depth coords inp hDL

theorem nonzeroProgram_ancillas_bound :
    (SequentialPipeline.nonzeroProgram coords inp hDL).value.sourceAncillas ≤ bound D L (inputBudget (L := L) (h := h) coords) ∧
    (SequentialPipeline.nonzeroProgram coords inp hDL).value.targetAncillas ≤ bound D L (inputBudget (L := L) (h := h) coords) :=
  ⟨nonzero_source_ancillas coords inp hDL,nonzero_target_ancillas coords inp hDL⟩

end Decoupling.HighDim.SequentialPipelineResource
