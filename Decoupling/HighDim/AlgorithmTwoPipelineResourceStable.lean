import Decoupling.HighDim.AlgorithmTwoPipelineResourceGamma
import Decoupling.HighDim.AlgorithmTwoPipelineFrame

/-! # C4 resources from the same original/stored target data
The only semantic inputs of the execution wrapper are the actual native
homotopy equivalence and its array representation. All size bounds are
derived here, including the true original term ranks and both tail sums.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipelineResource
noncomputable section
open HomologicalComplex
open AlgorithmTwoPipeline AlgorithmTwoResourceBudget AlgorithmTwoInputGrowth
open StableFree.Effective.CochainProgram StableFree.Resource
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
  (inp : Input (D := D) (L := L) (h := h) coords) (hDL : D ≤ L)
  (out : InputLayers coords inp hDL)

noncomputable abbrev targetOriginal := originalFromFrame (AlgorithmTwoToricData.totalCoordinates D out.multiplicities K)

abbrev nativeRadius := max (max out.commonRadius (gammaRadius coords inp hDL out))
  (AlgorithmTwoLinearComparison.resultBox D
    (AlgorithmTwoToricData.totalRank D out.multiplicities+inputRank coords L)
    (AlgorithmTwoToricData.totalRank D out.multiplicities+inputRank coords L) 0
    (max out.commonRadius (gammaRadius coords inp hDL out)))

omit [DecidableEq K] in
theorem original_term_cone (j : ℤ) :
    coords.rank j ≤ cone D (inputBudget (L := L) (h := h) coords) :=
  (term_rank_le coords j).trans ((input_le_layer D _).trans
    ((layer_le_comparison D _).trans (comparison_le_cone D _)))

theorem target_term_cone (j : ℤ) :
    (targetOriginal coords inp hDL out).rank j ≤ cone D (inputBudget (L := L) (h := h) coords) :=
  (gradeRank_le _ j).trans ((toric_rank_comparison coords inp hDL out).trans (comparison_le_cone D _))

variable (arrays : NativeArrays K D (inputRank coords L)
  (AlgorithmTwoToricData.totalRank D out.multiplicities) (nativeRadius coords inp hDL out))

abbrev targetTail := tailTower
  (selectorsFromDegree (AlgorithmTwoToricData.totalCoordinates D out.multiplicities K).degree)
  arrays.differentialT (L+1)
abbrev originalTail := tailTower (originalSelectors (L := L) coords) arrays.differentialC (L+1)
abbrev extraC := coords.rank 2+((targetOriginal coords inp hDL out).rank 1+
  ((targetTail coords inp hDL out arrays).ranks (originalTail coords inp hDL out arrays)).2)
abbrev extraT := coords.rank 2+(coords.rank 1+
  ((targetTail coords inp hDL out arrays).ranks (originalTail coords inp hDL out arrays)).1)
abbrev stableRadius := runBox (targetTail coords inp hDL out arrays) (originalTail coords inp hDL out arrays)
  (coords.rank 2) ((targetOriginal coords inp hDL out).rank 2) (nativeRadius coords inp hDL out)

/-- The actual C4 tail budget, derived from the original coordinates. -/
theorem native_budget :
    nativeBudget
      (tailTower (selectorsFromDegree (AlgorithmTwoToricData.totalCoordinates D out.multiplicities K).degree)
        arrays.differentialT (L+1))
      (tailTower (originalSelectors (L := L) coords) arrays.differentialC (L+1))
      (coords.rank 2) ((targetOriginal coords inp hDL out).rank 2)
      ((targetOriginal coords inp hDL out).rank 0) (nativeRadius coords inp hDL out) ≤
      (budgetPolynomial L).eval (cone D (inputBudget (L := L) (h := h) coords)) := by
  rw [budgetPolynomial_eval]
  exact uniform_native_budget (originalSelectors (L := L) coords)
    (selectorsFromDegree (AlgorithmTwoToricData.totalCoordinates D out.multiplicities K).degree)
    arrays L _ (original_term_cone coords) (target_term_cone coords inp hDL out)
    (c4_radius_numeric coords inp hDL out)

theorem stable_output_radius :
    runBox
      (tailTower (selectorsFromDegree (AlgorithmTwoToricData.totalCoordinates D out.multiplicities K).degree)
        arrays.differentialT (L+1))
      (tailTower (originalSelectors (L := L) coords) arrays.differentialC (L+1))
      (coords.rank 2) ((targetOriginal coords inp hDL out).rank 2) (nativeRadius coords inp hDL out) ≤
      stable D L (inputBudget (L := L) (h := h) coords) := by
  rw [stable_eq]
  apply (uniform_output_box (originalSelectors (L := L) coords)
    (selectorsFromDegree (AlgorithmTwoToricData.totalCoordinates D out.multiplicities K).degree)
    arrays L _ (original_term_cone coords) (target_term_cone coords inp hDL out)
    (c4_radius_numeric coords inp hDL out)).trans
  exact AlgorithmTwoStableFreeGrowth.box_le_bound D L _

theorem stable_output_ranks :
    let F := tailTower (selectorsFromDegree (AlgorithmTwoToricData.totalCoordinates D out.multiplicities K).degree)
      arrays.differentialT (L+1)
    let G := tailTower (originalSelectors (L := L) coords) arrays.differentialC (L+1)
    let extraC := coords.rank 2+((targetOriginal coords inp hDL out).rank 1+(F.ranks G).2)
    let extraT := coords.rank 2+(coords.rank 1+(F.ranks G).1)
    extraC ≤ stable D L (inputBudget (L := L) (h := h) coords) ∧
      extraT ≤ stable D L (inputBudget (L := L) (h := h) coords) ∧
      coords.rank 1+extraC ≤ stable D L (inputBudget (L := L) (h := h) coords) ∧
      (targetOriginal coords inp hDL out).rank 1+extraT ≤ stable D L (inputBudget (L := L) (h := h) coords) := by
  have hb := uniform_stabilized_ranks (originalSelectors (L := L) coords)
    (selectorsFromDegree (AlgorithmTwoToricData.totalCoordinates D out.multiplicities K).degree)
    arrays L _ (original_term_cone coords) (target_term_cone coords inp hDL out)
    (c4_radius_numeric coords inp hDL out)
  have hcap : (budgetPolynomial L).eval (cone D (inputBudget (L := L) (h := h) coords)) ≤
      stable D L (inputBudget (L := L) (h := h) coords) := by
    rw [stable_eq]
    exact AlgorithmTwoStableFreeGrowth.budget_le_bound D L _
  exact ⟨hb.1.trans hcap,hb.2.1.trans hcap,hb.2.2.1.trans hcap,hb.2.2.2.trans hcap⟩

variable [C.IsGE 1]
  [(AlgorithmTwoToricData.nativeStack D out.multiplicities K).IsGE 1]
  [(AlgorithmTwoToricData.nativeStack D out.multiplicities K).IsStrictlyGE (-(L:ℤ))]

/-- Full native C4 execution: input sign preparation, the initial quotient
stage, every tail stage, and absorption are all included by the trace. -/
theorem stable_execute_cost
    (e : HomotopyEquiv C (AlgorithmTwoToricData.nativeStack D out.multiplicities K))
    (ha : NativeRealizes (inputCoordinates (L := L) coords)
      (AlgorithmTwoToricData.totalCoordinates D out.multiplicities K) e arrays) :
    (execute coords (targetOriginal coords inp hDL out) (inputCoordinates (L := L) coords)
      (AlgorithmTwoToricData.totalCoordinates D out.multiplicities K)
      (originalSelectors (L := L) coords)
      (selectorsFromDegree (AlgorithmTwoToricData.totalCoordinates D out.multiplicities K).degree)
      (originalSelectors_realizes coords) (selectorsFromDegree_realizes _)
      e arrays ha L).cost ≤ stable D L (inputBudget (L := L) (h := h) coords) := by
  rw [stable_eq]
  exact (execute_uniform_polynomial coords (targetOriginal coords inp hDL out)
    (inputCoordinates (L := L) coords) (AlgorithmTwoToricData.totalCoordinates D out.multiplicities K)
    (originalSelectors (L := L) coords)
    (selectorsFromDegree (AlgorithmTwoToricData.totalCoordinates D out.multiplicities K).degree)
    (originalSelectors_realizes coords) (selectorsFromDegree_realizes _) e arrays ha L _
    (original_term_cone coords) (target_term_cone coords inp hDL out)
    (c4_radius_numeric coords inp hDL out)).trans (AlgorithmTwoStableFreeGrowth.cost_le_bound D L _)

end
end Decoupling.HighDim.AlgorithmTwoPipelineResource
