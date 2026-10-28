import Decoupling.HighDim.SequentialPipelineCone
import Decoupling.HighDim.AlgorithmTwoPipelineC4Data
import Decoupling.HighDim.AlgorithmTwoPipelineSelectors
import Decoupling.HighDim.AlgorithmTwoToricDataSupport

/- HD016: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of Algorithm 2”.
New sequential-contraction execution; historical AlgorithmTwoPipelineC4 is preserved. -/
/-! # The solved cone supplies every C4 premise internally -/
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

/-- Explicit filtered original ranks, evaluated only from integer labels. -/
def targetRank : ℤ → ℕ := gradeRank (AlgorithmTwoToricData.degrees D s.multiplicities)

def nativeArrays : NativeArrays K D (inputRank cC L)
    (AlgorithmTwoToricData.totalRank D s.multiplicities) (c4Radius cC inp hDL s) where
  differentialC := LaurentArithmetic.matrixPad inp.differential _
  differentialT := LaurentArithmetic.matrixPad t.differential _
  hom := LaurentArithmetic.matrixPad x.arrays.inverse _
  inv := LaurentArithmetic.matrixPad g.matrix _
  homotopyC := LaurentArithmetic.matrixPad x.arrays.targetHomotopy _
  homotopyT := LaurentArithmetic.matrixPad x.arrays.sourceHomotopy _

noncomputable section

theorem target_lower_bound : (AlgorithmTwoToricData.nativeStack D s.multiplicities K).IsStrictlyGE (-(L:ℤ)) := by
  let : (AlgorithmTwoToricData.nativeStack D s.multiplicities K).IsStrictlyGE (-(D:ℤ)) :=
    (AlgorithmTwoToricData.nativeStack_bounds D s.multiplicities K).1
  exact CochainComplex.isStrictlyGE_of_ge _ (-(L:ℤ)) (-(D:ℤ)) (by omega)

theorem nativeArrays_realizes : NativeRealizes (inputCoordinates (L := L) cC)
    (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K)
    (computedEquivalence cC inp hDL s t g H).symm (nativeArrays cC inp hDL s t g H x) := by
  have hInput : h ≤ c4Radius cC inp hDL s := s.input_le_commonRadius.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hOne : 1 ≤ c4Radius cC inp hDL s := s.one_le_commonRadius.trans ((le_max_left _ _).trans (le_max_left _ _))
  have hGamma : gammaRadius cC inp hDL s ≤ c4Radius cC inp hDL s := (le_max_right _ _).trans (le_max_left _ _)
  have hH : homotopyRadius cC inp hDL s ≤ c4Radius cC inp hDL s := le_max_right _ _
  constructor
  · change (inputCoordinates (L := L) cC).RepresentsDifferential (LaurentArithmetic.matrixDenote (LaurentArithmetic.matrixPad inp.differential _))
    rw [LaurentArithmetic.matrixPad_correct _ hInput]
    exact inp.represents
  · change (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K).RepresentsDifferential
      (LaurentArithmetic.matrixDenote (LaurentArithmetic.matrixPad t.differential _))
    rw [LaurentArithmetic.matrixPad_correct _ hOne]
    exact storedTarget_represents cC inp hDL s t
  · intro j v
    change LaurentArithmetic.matrixDenote (LaurentArithmetic.matrixPad x.arrays.inverse _) *ᵥ _ = _
    rw [LaurentArithmetic.matrixPad_correct _ hH,x.correct,AlgorithmTwoLinearComparison.extractProgram_inverse]
    exact blockHomotopyEquiv_inv_represents (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K) (inputCoordinates (L := L) cC)
      _ _ (storedTarget_represents cC inp hDL s t) inp.represents (gammaMap cC inp hDL s t g)
      _ (gammaMap_represents cC inp hDL s t g) _ H.homogeneous H.equation j v
  · intro j v
    change LaurentArithmetic.matrixDenote (LaurentArithmetic.matrixPad g.matrix _) *ᵥ _ = _
    rw [LaurentArithmetic.matrixPad_correct _ hGamma]
    exact gammaMap_represents cC inp hDL s t g j v
  · intro a b hab v
    change LaurentArithmetic.matrixDenote (LaurentArithmetic.matrixPad x.arrays.targetHomotopy _) *ᵥ _ = _
    rw [LaurentArithmetic.matrixPad_correct _ hH,x.correct,AlgorithmTwoLinearComparison.extractProgram_target]
    exact blockHomotopyEquiv_target_represents (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K) (inputCoordinates (L := L) cC)
      _ _ (storedTarget_represents cC inp hDL s t) inp.represents (gammaMap cC inp hDL s t g)
      _ (gammaMap_represents cC inp hDL s t g) _ H.homogeneous H.equation a b hab v
  · intro a b hab v
    change LaurentArithmetic.matrixDenote (LaurentArithmetic.matrixPad x.arrays.sourceHomotopy _) *ᵥ _ = _
    rw [LaurentArithmetic.matrixPad_correct _ hH,x.correct,AlgorithmTwoLinearComparison.extractProgram_source]
    exact blockHomotopyEquiv_source_represents (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K) (inputCoordinates (L := L) cC)
      _ _ (storedTarget_represents cC inp hDL s t) inp.represents (gammaMap cC inp hDL s t g)
      _ (gammaMap_represents cC inp hDL s t g) _ H.homogeneous H.equation a b hab v

theorem stable_ready : C4Ready (originalSelectors (L := L) cC)
    (selectorsFromDegree (AlgorithmTwoToricData.degrees D s.multiplicities))
    (nativeArrays cC inp hDL s t g H x) L := by
  let : C.IsGE 1 := input_isGE cC inp
  let : (AlgorithmTwoToricData.nativeStack D s.multiplicities K).IsGE 1 :=
    AlgorithmTwoToricData.nativeStack_isGE_one D s.multiplicities K
  let : (AlgorithmTwoToricData.nativeStack D s.multiplicities K).IsStrictlyGE (-(L:ℤ)) := target_lower_bound cC inp hDL s
  exact c4Ready_of_native cC (originalFromFrame (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K))
    (inputCoordinates (L := L) cC) (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K)
    (originalSelectors (L := L) cC) (selectorsFromDegree (AlgorithmTwoToricData.degrees D s.multiplicities))
    (originalSelectors_realizes cC) (selectorsFromDegree_realizes _)
    (computedEquivalence cC inp hDL s t g H).symm (nativeArrays cC inp hDL s t g H x)
    (nativeArrays_realizes cC inp hDL s t g H x) L

end

def stableProgram := c4DataProgram (originalSelectors (L := L) cC)
  (selectorsFromDegree (AlgorithmTwoToricData.degrees D s.multiplicities))
  (nativeArrays cC inp hDL s t g H x) L (stable_ready cC inp hDL s t g H x)

noncomputable section

theorem stableProgram_eq_execute
    [C.IsGE 1] [(AlgorithmTwoToricData.nativeStack D s.multiplicities K).IsGE 1]
    [(AlgorithmTwoToricData.nativeStack D s.multiplicities K).IsStrictlyGE (-(L:ℤ))] :
    stableProgram cC inp hDL s t g H x =
      execute cC (originalFromFrame (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K))
        (inputCoordinates (L := L) cC) (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K)
        (originalSelectors (L := L) cC) (selectorsFromDegree (AlgorithmTwoToricData.degrees D s.multiplicities))
        (originalSelectors_realizes cC) (selectorsFromDegree_realizes _)
        (computedEquivalence cC inp hDL s t g H).symm (nativeArrays cC inp hDL s t g H x)
        (nativeArrays_realizes cC inp hDL s t g H x) L := rfl

end
end Decoupling.HighDim.SequentialPipeline
