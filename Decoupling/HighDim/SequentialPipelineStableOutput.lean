import Decoupling.HighDim.SequentialPipelineC4
import Decoupling.HighDim.AlgorithmTwoInvertiblePresentations
import Decoupling.HighDim.AlgorithmTwoInvertibleMatrices

/- HD016: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of Algorithm 2”.
New sequential-contraction execution; historical AlgorithmTwoPipelineStableOutput is preserved. -/
/-! # Stored C4 output and internally proved solvability of all four lifts -/
namespace Decoupling.HighDim.SequentialPipeline
open AlgorithmTwoPipeline
open CategoryTheory HomologicalComplex Matrix ArithmeticCost AlgorithmTwoFiniteComplex
open StableFree.Effective StableFree.Effective.CochainProgram
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
variable (inp : Input (D := D) (L := L) (h := h) cC) (hDL : D ≤ L)
variable (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
  (g : StoredGamma cC inp hDL s t) (H : StoredHomotopy cC inp hDL s t g)
  (x : StoredExtraction cC inp hDL s t g H)

abbrev nativeTargetTail := tailTower (selectorsFromDegree (AlgorithmTwoToricData.degrees D s.multiplicities))
  (nativeArrays cC inp hDL s t g H x).differentialT (L+1)
abbrev nativeOriginalTail := tailTower (originalSelectors (L := L) cC)
  (nativeArrays cC inp hDL s t g H x).differentialC (L+1)
abbrev stableExtraC := cC.rank 2+(targetRank cC inp hDL s 1+
  ((nativeTargetTail cC inp hDL s t g H x).ranks (nativeOriginalTail cC inp hDL s t g H x)).2)
abbrev stableExtraT := cC.rank 2+(cC.rank 1+
  ((nativeTargetTail cC inp hDL s t g H x).ranks (nativeOriginalTail cC inp hDL s t g H x)).1)
abbrev stableBox := runBox (nativeTargetTail cC inp hDL s t g H x) (nativeOriginalTail cC inp hDL s t g H x)
  (cC.rank 2) (targetRank cC inp hDL s 2) (c4Radius cC inp hDL s)
abbrev StableOutput := Output K D (cC.rank 1) (cC.rank 0) (targetRank cC inp hDL s 1) (targetRank cC inp hDL s 0)
  (stableExtraC cC inp hDL s t g H x) (stableExtraT cC inp hDL s t g H x) (stableBox cC inp hDL s t g H x)

/-- The actual stable beta is used only within this proposition proof. -/
theorem stable_fourSolvable :
    let o := (stableProgram cC inp hDL s t g H x).value
    AlgorithmTwoInvertible.FourSolvable (LaurentArithmetic.matrixDenote o.dC) (LaurentArithmetic.matrixDenote o.dT)
      (LaurentArithmetic.matrixDenote o.forward) (LaurentArithmetic.matrixDenote o.inverse) := by
  let : C.IsGE 1 := input_isGE cC inp
  let : (AlgorithmTwoToricData.nativeStack D s.multiplicities K).IsGE 1 :=
    AlgorithmTwoToricData.nativeStack_isGE_one D s.multiplicities K
  let : (AlgorithmTwoToricData.nativeStack D s.multiplicities K).IsStrictlyGE (-(L:ℤ)) := target_lower_bound cC inp hDL s
  have hc := execute_correct cC (originalFromFrame (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K))
    (inputCoordinates (L := L) cC) (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K)
    (originalSelectors (L := L) cC) (selectorsFromDegree (AlgorithmTwoToricData.degrees D s.multiplicities))
    (originalSelectors_realizes cC) (selectorsFromDegree_realizes _)
    (computedEquivalence cC inp hDL s t g H).symm (nativeArrays cC inp hDL s t g H x)
    (nativeArrays_realizes cC inp hDL s t g H x) L
  rw [← stableProgram_eq_execute cC inp hDL s t g H x] at hc
  obtain ⟨beta,hC,hT,hF,hG⟩ := hc
  exact AlgorithmTwoInvertible.fixed_presentations_lifts _ _ _ _ hC hT beta _ _ hF hG

structure StoredStable where
  arrays : StableOutput cC inp hDL s t g H x
  correct : arrays = (stableProgram cC inp hDL s t g H x).value

def storeStableProgram : Work K (StoredStable cC inp hDL s t g H x) :=
  let run := stableProgram cC inp hDL s t g H x
  { value := ⟨run.value,rfl⟩, trace := run.trace }

theorem storeStableProgram_cost : (storeStableProgram cC inp hDL s t g H x).cost =
    (stableProgram cC inp hDL s t g H x).cost := rfl

theorem storedStable_solvable (u : StoredStable cC inp hDL s t g H x) :
    AlgorithmTwoInvertible.FourSolvable (LaurentArithmetic.matrixDenote u.arrays.dC) (LaurentArithmetic.matrixDenote u.arrays.dT)
      (LaurentArithmetic.matrixDenote u.arrays.forward) (LaurentArithmetic.matrixDenote u.arrays.inverse) := by
  rw [u.correct]
  exact stable_fourSolvable cC inp hDL s t g H x

/-- The four actual scalar-system solves, with their premises now discharged. -/
def liftProgram (u : StoredStable cC inp hDL s t g H x) :=
  AlgorithmTwoInvertible.liftMatricesProgram u.arrays.dC u.arrays.dT u.arrays.forward u.arrays.inverse
    (storedStable_solvable cC inp hDL s t g H x u)

end Decoupling.HighDim.SequentialPipeline
