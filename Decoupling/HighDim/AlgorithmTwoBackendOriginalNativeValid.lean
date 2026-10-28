import Decoupling.HighDim.AlgorithmTwoBackendOriginalNative
import Decoupling.HighDim.AlgorithmTwoPipelineBackend

/-! # Original formality supplies validity of the exact stored raw arrays
No native complex is replaced by a proxy. The isomorphism is the explicit
original coordinate isomorphism, and all validity data are propositions.
-/
namespace Decoupling.HighDim.AlgorithmTwoBackendOriginal
open CategoryTheory AlgorithmTwoPipelineBackend
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {K : Type} [Field K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
  (inp : AlgorithmTwoOriginalArrays.Input (D := D) (L := L) (h := h) coords)

theorem raw_formal : Formal (rawInput coords inp) (raw_squareZero coords inp) := by
  obtain ⟨old,⟨e⟩⟩ := inp.formal
  exact ⟨old,⟨e ≪≫ DerivedCategory.Q.mapIso (originalNativeIso coords inp)⟩⟩

/-- The original chain equations and original formal profile discharge
both backend validity requirements, with no new hypothesis. -/
theorem raw_valid : Valid (rawInput coords inp) :=
  ⟨raw_squareZero coords inp,raw_formal coords inp⟩

end Decoupling.HighDim.AlgorithmTwoBackendOriginal
