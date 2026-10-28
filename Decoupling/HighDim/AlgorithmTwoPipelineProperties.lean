import Decoupling.HighDim.AlgorithmTwoPipelineInput
import Decoupling.HighDim.AlgorithmTwoPipelineLayers

/-! # Native properties derived internally from the original formal profile -/
namespace Decoupling.HighDim.AlgorithmTwoPipeline
open CategoryTheory CategoryTheory.Limits HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {K : Type} [Field K] {D L h : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
variable (inp : Input (D := D) (L := L) (h := h) cC)

include inp in
theorem input_isGE : C.IsGE 1 := by
  obtain ⟨old,⟨e⟩⟩ := inp.formal
  rw [CochainComplex.isGE_iff]
  intro j hj
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact AlgorithmTwoComputedLayers.nativeHomology_outside K D old e j (by
    rintro ⟨k,hk⟩
    omega)

include inp in
theorem input_augmentation (j : ℤ) : TrivialLayers.AugmentationAction (C.homology j) := by
  obtain ⟨old,⟨e⟩⟩ := inp.formal
  exact AlgorithmTwoComputedLayers.nativeHomology_augmentation K D old e j

variable [DecidableEq K] (hDL : D ≤ L)

def computeLayers : ArithmeticCost.Work K
    (StoredLayers cC (incoming cC inp hDL) (outgoing cC inp hDL)) :=
  storedLayersProgram cC (incoming cC inp hDL) (outgoing cC inp hDL)

theorem storedLayer_correct
    (s : StoredLayers cC (incoming cC inp hDL) (outgoing cC inp hDL)) (j : Fin (D-1)) :
    AlgorithmTwoCohomology.Correct (LaurentArithmetic.matrixDenote (incoming cC inp hDL j))
      (LaurentArithmetic.matrixDenote (outgoing cC inp hDL j))
      (AlgorithmTwoComputedLayers.outputWindowSquare cC (incoming cC inp hDL) (outgoing cC inp hDL)
        (incoming_action cC inp hDL) (outgoing_action cC inp hDL) j) (s.result j) := by
  rw [s.result_correct]
  obtain ⟨old,⟨e⟩⟩ := inp.formal
  exact AlgorithmTwoComputedLayers.output_correct cC old e (incoming cC inp hDL) (outgoing cC inp hDL)
    (incoming_action cC inp hDL) (outgoing_action cC inp hDL) j

end Decoupling.HighDim.AlgorithmTwoPipeline
