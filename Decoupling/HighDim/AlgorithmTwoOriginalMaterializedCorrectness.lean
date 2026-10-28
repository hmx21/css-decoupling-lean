import Decoupling.HighDim.AlgorithmTwoOriginalMaterialized
import Decoupling.HighDim.AlgorithmTwoBackendCorrectnessPhysical

/-!
# The public finite-vector output belongs to the actual original complex

The original-coordinate cochain isomorphism transfers native homology
and the actual computed target back to C. Physical correctness is the
already proved two-branch statement for those same stored original arrays.
-/
namespace Decoupling.HighDim.AlgorithmTwoBackendOriginal
open CategoryTheory HomologicalComplex AlgorithmTwoPipelineBackend
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem nativeComplex_congr {K : Type} [Field K] {D L h : ℕ}
    (a b : RawInput K D L h) (he : a=b) (ha : SquareZero a) (hb : SquareZero b) :
    nativeComplex a ha = nativeComplex b hb := by
  subst b
  rfl

variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
  (inp : AlgorithmTwoOriginalArrays.Input (D := D) (L := L) (h := h) coords)

def materializedNativeIso :
    C ≅ model (materializedInput coords inp).toRaw (materialized_valid coords inp) :=
  originalNativeIso coords inp ≪≫ eqToIso (nativeComplex_congr
    (rawInput coords inp) (materializedInput coords inp).toRaw
    (RawInput.materialize_toRaw _).symm (raw_squareZero coords inp)
    (Classical.choose (materialized_valid coords inp)))

def materializedHomologyCoefficientsIso (j : ℤ) :
    Layers.coefficients (C.homology j) ≅
      Layers.coefficients ((model (materializedInput coords inp).toRaw
        (materialized_valid coords inp)).homology j) :=
  (ModuleCat.restrictScalars constant).mapIso
    ((homologyFunctor (ModuleCat (Laurent K D)) (.up ℤ) j).mapIso (materializedNativeIso coords inp))

theorem original_materialized_multiplicities (hDL : D ≤ L) (j : Fin (D-1)) :
    (executeMaterialized (materializedInput coords inp) (materialized_valid coords inp) hDL).value.multiplicities.get j =
      Module.finrank K (Layers.coefficients (C.homology (j.val+1))) := by
  have hr := executeMaterialized_multiplicities hDL (materializedInput coords inp)
    (materialized_valid coords inp) j
  exact hr.trans (materializedHomologyCoefficientsIso coords inp (j.val+1)).toLinearEquiv.finrank_eq.symm

theorem original_materialized_nativeEquivalence (hDL : D ≤ L) :
    Nonempty (HomotopyEquiv
      (AlgorithmTwoToricData.nativeStack D
        (executeMaterialized (materializedInput coords inp) (materialized_valid coords inp) hDL).value.multiplicities K)
      C) := by
  obtain ⟨e⟩ := executeMaterialized_nativeEquivalence hDL (materializedInput coords inp)
    (materialized_valid coords inp)
  exact ⟨e.trans (HomotopyEquiv.ofIso (materializedNativeIso coords inp).symm)⟩

end
end Decoupling.HighDim.AlgorithmTwoBackendOriginal

namespace Decoupling.HighDim.AlgorithmTwoBackendOriginal
open AlgorithmTwoPipelineBackend
variable {p D L h : ℕ} [Fact p.Prime]
  {C : CochainComplex (ModuleCat (Laurent (ZMod p) D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
  (inp : AlgorithmTwoOriginalArrays.Input (D := D) (L := L) (h := h) coords)

/-- Both physical branches for the same original coefficient data; the
backend validity proof is derived here rather than supplied as a premise. -/
theorem original_materialized_physical (hDL : D ≤ L)
    (Cells : Type*) [Fintype Cells] [DecidableEq Cells] :
    ZeroPhysicalOutput (materializedInput coords inp).toRaw (materialized_valid coords inp) hDL Cells ∨
      NonzeroPhysicalOutput (materializedInput coords inp).toRaw (materialized_valid coords inp) hDL Cells :=
  executeMaterialized_physical_cases hDL Cells (materializedInput coords inp) (materialized_valid coords inp)

end Decoupling.HighDim.AlgorithmTwoBackendOriginal
