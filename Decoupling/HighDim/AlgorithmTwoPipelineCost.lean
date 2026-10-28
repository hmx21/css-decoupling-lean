import Decoupling.HighDim.AlgorithmTwoPipelineCostStages
import Decoupling.HighDim.AlgorithmTwoPipelineResourceStored
import Decoupling.HighDim.AlgorithmTwoPipelineResourcePhysical
import Decoupling.HighDim.AlgorithmTwoPipelineProgram

/-!
# Polynomial resources of the same complete executable Algorithm 2

This closes the trace composition: every stage is evaluated by the real
program, with its stored outputs shared by the next stage. No map,
homotopy, stable isomorphism, solver certificate, intermediate size bound,
or polynomial-cost certificate is a caller-supplied premise.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipelineResource
open AlgorithmTwoPipeline AlgorithmTwoResourceBudget AlgorithmTwoInputGrowth ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
  (inp : Input (D := D) (L := L) (h := h) coords) (hDL : D ≤ L)

theorem stages_cost_decomposition :
    let q := (stagesProgram coords inp hDL).value
    (stagesProgram coords inp hDL).cost =
      (computeLayers coords inp hDL).cost+(storeTargetProgram coords inp hDL q.layers).cost+
      (gammaProgram coords inp hDL q.layers q.target).cost+
      (homotopyProgram coords inp hDL q.layers q.target q.gamma).cost+
      (extractionProgram coords inp hDL q.layers q.target q.gamma q.homotopy).cost+
      (storeStableProgram coords inp hDL q.layers q.target q.gamma q.homotopy q.extraction).cost := by
  simp only [stagesProgram, Work.bind_cost, Work.pure_cost, Work.bind_value, Work.pure_value]
  omega

theorem stages_cost : (stagesProgram coords inp hDL).cost ≤
    1+layer D (inputBudget (L := L) (h := h) coords)+comparison D (inputBudget (L := L) (h := h) coords)+
      cone D (inputBudget (L := L) (h := h) coords)+stable D L (inputBudget (L := L) (h := h) coords) := by
  let q := (stagesProgram coords inp hDL).value
  have hp := prefix_cost coords inp hDL q.layers q.target q.gamma q.homotopy
  have hs := stored_stable_cost coords inp hDL q.layers q.target q.gamma q.homotopy q.extraction
  rw [stages_cost_decomposition]
  exact Nat.add_le_add hp hs

theorem finish_cost (q : Stages coords inp hDL) :
    (finishProgram coords inp hDL q).cost ≤ lift D L (inputBudget (L := L) (h := h) coords) := by
  rw [finishProgram_cost]
  have hh := stored_lift_theta_cost coords inp hDL q.layers q.target q.gamma q.homotopy q.extraction q.stable
  rw [Work.bind_cost] at hh
  exact hh

theorem nonzero_cost : (nonzeroProgram coords inp hDL).cost ≤ bound D L (inputBudget (L := L) (h := h) coords) := by
  rw [nonzeroProgram_cost, bound_eq]
  have hs := stages_cost coords inp hDL
  have hf := finish_cost coords inp hDL (stagesProgram coords inp hDL).value
  omega

theorem finish_depth (q : Stages coords inp hDL) :
    (finishProgram coords inp hDL q).value.gates.length ≤ bound D L (inputBudget (L := L) (h := h) coords) :=
  (stored_lift_theta_depth coords inp hDL q.layers q.target q.gamma q.homotopy q.extraction q.stable).trans
    (lift_le_bound D L _)

theorem finish_source_ancillas (q : Stages coords inp hDL) :
    (finishProgram coords inp hDL q).value.sourceAncillas ≤ bound D L (inputBudget (L := L) (h := h) coords) :=
  (source_ancilla_count coords inp hDL q.layers
    (nativeArrays coords inp hDL q.layers q.target q.gamma q.homotopy q.extraction)).trans (lift_le_bound D L _)

theorem finish_target_ancillas (q : Stages coords inp hDL) :
    (finishProgram coords inp hDL q).value.targetAncillas ≤ bound D L (inputBudget (L := L) (h := h) coords) :=
  (target_ancilla_count coords inp hDL q.layers
    (nativeArrays coords inp hDL q.layers q.target q.gamma q.homotopy q.extraction)).trans (lift_le_bound D L _)

theorem finish_species (q : Stages coords inp hDL) :
    (finishProgram coords inp hDL q).value.species ≤ bound D L (inputBudget (L := L) (h := h) coords) :=
  (physical_width coords inp hDL q.layers
    (nativeArrays coords inp hDL q.layers q.target q.gamma q.homotopy q.extraction)).trans (lift_le_bound D L _)

theorem nonzero_depth : (nonzeroProgram coords inp hDL).value.gates.length ≤
    bound D L (inputBudget (L := L) (h := h) coords) :=
  finish_depth coords inp hDL (stagesProgram coords inp hDL).value

theorem nonzero_source_ancillas : (nonzeroProgram coords inp hDL).value.sourceAncillas ≤
    bound D L (inputBudget (L := L) (h := h) coords) :=
  finish_source_ancillas coords inp hDL (stagesProgram coords inp hDL).value

theorem nonzero_target_ancillas : (nonzeroProgram coords inp hDL).value.targetAncillas ≤
    bound D L (inputBudget (L := L) (h := h) coords) :=
  finish_target_ancillas coords inp hDL (stagesProgram coords inp hDL).value

theorem nonzero_species : (nonzeroProgram coords inp hDL).value.species ≤
    bound D L (inputBudget (L := L) (h := h) coords) :=
  finish_species coords inp hDL (stagesProgram coords inp hDL).value

/-- One common polynomial bounds the actual complete trace, the returned
SUM/SWAP depth, both actual added-qudit counts, and physical width. -/
theorem nonzero_resources :
    let run := nonzeroProgram coords inp hDL
    let B := (AlgorithmTwoResourceBudget.polynomial D L).eval (inputBudget (L := L) (h := h) coords)
    run.cost ≤ B ∧ run.value.gates.length ≤ B ∧ run.value.sourceAncillas ≤ B ∧
      run.value.targetAncillas ≤ B ∧ run.value.species ≤ B :=
  ⟨nonzero_cost coords inp hDL,nonzero_depth coords inp hDL,nonzero_source_ancillas coords inp hDL,
    nonzero_target_ancillas coords inp hDL,nonzero_species coords inp hDL⟩

theorem nonzeroProgram_cost_bound : (nonzeroProgram coords inp hDL).cost ≤
    bound D L (inputBudget (L := L) (h := h) coords) := nonzero_cost coords inp hDL

theorem nonzeroProgram_depth_bound : (nonzeroProgram coords inp hDL).value.gates.length ≤
    bound D L (inputBudget (L := L) (h := h) coords) := nonzero_depth coords inp hDL

theorem nonzeroProgram_ancillas_bound :
    (nonzeroProgram coords inp hDL).value.sourceAncillas ≤ bound D L (inputBudget (L := L) (h := h) coords) ∧
    (nonzeroProgram coords inp hDL).value.targetAncillas ≤ bound D L (inputBudget (L := L) (h := h) coords) :=
  ⟨nonzero_source_ancillas coords inp hDL,nonzero_target_ancillas coords inp hDL⟩

end Decoupling.HighDim.AlgorithmTwoPipelineResource
