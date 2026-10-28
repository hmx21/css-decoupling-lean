import Decoupling.HighDim.SequentialProgram
import Decoupling.HighDim.SequentialPipelineCost

/-!
Source: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of
Algorithm 2”. This endpoint runs the new descending-contraction pipeline.

# HD016 Proposition 1 in the exact original dense coefficient count

The polynomial depends only on spatial dimension. It bounds the actual
complete execution from original adjacent arrays, the same returned
SUM/SWAP word, and both actual ancillary-qudit counts. The zero-size case
uses the literal empty branch and imposes no bound on its supplied radius.

The input is the already coarse-grained finite free complex of Algorithm 2.
Its canonical bounds ±(D+2) and formality follow from Algorithm 1 via
AlgorithmOnePipelineBridge. No assertion about Algorithm 1's cost,
bit complexity, or minimal-lattice search is made here.
-/
namespace Decoupling.HighDim.SequentialAlgorithmTwo
open AlgorithmTwoPipeline SequentialPipeline AlgorithmTwoInputGrowth SequentialResourceBudget
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 2000000
variable {K : Type} [Field K] [DecidableEq K] {D h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-((D+2 : ℕ):ℤ))] [C.IsStrictlyLE ((D+2 : ℕ):ℤ)]
  (inp : AlgorithmTwoOriginalArrays.Input (D := D) (L := D+2) (h := h) coords)

/-- The exact same polynomial controls all five actual resources.
The only nonzero-size premise used internally is discharged by the
program's own branch, not required from the caller. -/
theorem polynomial_cost (hD : 2 ≤ D) :
    let run := program coords inp (by omega : D ≤ D+2)
    let N := AlgorithmTwoOriginalArrays.coefficientCount (D := D) (L := D+2) (h := h) coords
    let B := (paperPolynomial D).eval N
    run.cost ≤ B ∧ run.value.gates.length ≤ B ∧ run.value.sourceAncillas ≤ B ∧
      run.value.targetAncillas ≤ B ∧ run.value.species ≤ B := by
  dsimp only
  by_cases hz : inputRank coords (D+2) = 0
  · rw [program_zero coords inp _ hz]
    exact ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
  · rw [program_nonzero coords inp _ hz]
    have hp : 0 < inputRank coords (D+2) := Nat.pos_of_ne_zero hz
    have hbudget := inp.dense_budget coords (by omega : 0 < D) hp
    have hpaper := SequentialResourceBudget.paper_bound (D := D)
      (s := inputBudget (L := D+2) (h := h) coords)
      (N := AlgorithmTwoOriginalArrays.coefficientCount (D := D) (L := D+2) (h := h) coords) hbudget
    have hrun := SequentialPipelineResource.nonzero_resources coords (inp.toPipeline coords) (by omega : D ≤ D+2)
    exact ⟨hrun.1.trans hpaper,hrun.2.1.trans hpaper,hrun.2.2.1.trans hpaper,
      hrun.2.2.2.1.trans hpaper,hrun.2.2.2.2.trans hpaper⟩

end Decoupling.HighDim.SequentialAlgorithmTwo

namespace Decoupling.HighDim.SequentialAlgorithmTwo

/-- Proposition 1 with an explicit quantifier order: one polynomial for
each fixed D, uniformly over fields, original arrays and their radius.
Only the original Algorithm 2 input conditions occur. -/
theorem proposition_one (D : ℕ) (hD : 2 ≤ D) :
    ∃ P : Polynomial ℕ,
      ∀ (K : Type) [Field K] [DecidableEq K] (h : ℕ)
        (C : CochainComplex (ModuleCat (Laurent K D)) ℤ)
        (coords : StableFree.Coordinates C)
        [C.IsStrictlyGE (-((D+2 : ℕ):ℤ))] [C.IsStrictlyLE ((D+2 : ℕ):ℤ)]
        (inp : AlgorithmTwoOriginalArrays.Input (D := D) (L := D+2) (h := h) coords),
        let run := program coords inp (by omega : D ≤ D+2)
        let N := AlgorithmTwoOriginalArrays.coefficientCount (D := D) (L := D+2) (h := h) coords
        run.cost ≤ P.eval N ∧ run.value.gates.length ≤ P.eval N ∧
          run.value.sourceAncillas ≤ P.eval N ∧ run.value.targetAncillas ≤ P.eval N := by
  refine ⟨SequentialResourceBudget.paperPolynomial D,?_⟩
  intro K instK instDec h C coords instLower instUpper inp
  have hres := polynomial_cost coords inp hD
  exact ⟨hres.1,hres.2.1,hres.2.2.1,hres.2.2.2.1⟩

end Decoupling.HighDim.SequentialAlgorithmTwo
