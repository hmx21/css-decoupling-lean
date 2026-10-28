import Decoupling.HighDim.GluedNativeFormality
import Decoupling.HighDim.GluedRankLoss
import Decoupling.HighDim.GluedProbeDimensions
import Decoupling.HighDim.TorusYonedaDetection

/-!
# The actual restricted example triangle and its counting spaces

Every object and connecting map is obtained by the genuine exact scalar
restriction functor applied to the actual native cone triangle.
-/

namespace Decoupling.HighDim.Glued

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Koszul KoszulLattice Torus GluedRankLoss
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (a : Translation 3 →+ Translation 3)

abbrev exampleRestriction := ModuleCat.restrictScalars (latticeMap K a)

def restrictedTriangle : Triangle (Derived K 3) :=
  (exampleRestriction K a).mapDerivedCategory.mapTriangle.obj (couplingTriangle K)

theorem restrictedTriangle_distinguished : restrictedTriangle K a ∈ distTriang _ :=
  (exampleRestriction K a).mapDerivedCategory.map_distinguished _ (couplingTriangle_distinguished K)

def restrictedLeftIso : (restrictedTriangle K a).obj₁ ≅
    (DerivedCategory.singleFunctor (ModuleCat (Laurent K 3)) 1).obj (coefficientModule K 3) :=
  (exampleRestriction K a).mapDerivedCategory.mapIso (couplingTriangleLeftIso K) ≪≫
    ((exampleRestriction K a).mapDerivedCategorySingleFunctor 1).app _ ≪≫
      (DerivedCategory.singleFunctor _ 1).mapIso (latticeCoefficientIso K a).symm

def restrictedRightIso : (restrictedTriangle K a).obj₃ ≅
    (DerivedCategory.singleFunctor (ModuleCat (Laurent K 3)) 2).obj (coefficientModule K 3) :=
  (exampleRestriction K a).mapDerivedCategory.mapIso (couplingTriangleRightIso K) ≪≫
    ((exampleRestriction K a).mapDerivedCategorySingleFunctor 2).app _ ≪≫
      (DerivedCategory.singleFunctor _ 2).mapIso (latticeCoefficientIso K a).symm

def restrictedProfileIso : (exampleRestriction K a).mapDerivedCategory.obj
    (Profile.S_X (checks K)) ≅ (restrictedTriangle K a).obj₂ :=
  (exampleRestriction K a).mapDerivedCategory.mapIso (actualProfileConeIso K)

def restrictedIncomingIso : (restrictedTriangle K a).invRotate.obj₁ ≅ probe K 3 :=
  (shiftFunctor (Derived K 3) (-1 : ℤ)).mapIso (restrictedRightIso K a) ≪≫
    ((DerivedCategory.singleFunctors (ModuleCat (Laurent K 3))).shiftIso
      (-1) 3 2 (by norm_num)).app (coefficientModule K 3)

def restrictedOutgoingIso : ((restrictedTriangle K a).obj₁)⟦(1 : ℤ)⟧ ≅
    (DerivedCategory.singleFunctor (ModuleCat (Laurent K 3)) 0).obj (coefficientModule K 3) :=
  (shiftFunctor (Derived K 3) (1 : ℤ)).mapIso (restrictedLeftIso K a) ≪≫
    ((DerivedCategory.singleFunctors (ModuleCat (Laurent K 3))).shiftIso
      1 0 1 (by norm_num)).app (coefficientModule K 3)

theorem restrictedConnecting_zero_iff : (restrictedTriangle K a).mor₃ = 0 ↔
    (couplingClass K).mapExactFunctor (exampleRestriction K a) = 0 := by
  change (exampleRestriction K a).mapDerivedCategory.map (couplingTriangle K).mor₃ ≫ _ = 0 ↔ _
  rw [CategoryTheory.Preadditive.IsIso.comp_right_eq_zero]
  exact couplingTriangle_mapped_zero_iff K a

instance restrictedLeft_finite : Module.Finite K
    (homCoefficients (probe K 3) (restrictedTriangle K a).obj₁) := by
  let := probeSingle_finite (coefficientModule K 3) 1 1 (by decide)
  exact Module.Finite.equiv (homCoefficientsIso (probe K 3) (restrictedLeftIso K a)).symm.toLinearEquiv

instance restrictedRight_finite : Module.Finite K
    (homCoefficients (probe K 3) (restrictedTriangle K a).obj₃) := by
  let := probeSingle_finite (coefficientModule K 3) 2 0 (by decide)
  exact Module.Finite.equiv (homCoefficientsIso (probe K 3) (restrictedRightIso K a)).symm.toLinearEquiv

instance restrictedIncoming_finite : Module.Finite K
    (homCoefficients (probe K 3) (restrictedTriangle K a).invRotate.obj₁) :=
  Module.Finite.equiv (homCoefficientsIso (probe K 3) (restrictedIncomingIso K a)).symm.toLinearEquiv

instance restrictedOutgoing_finite : Module.Finite K
    (homCoefficients (probe K 3) (((restrictedTriangle K a).obj₁)⟦(1 : ℤ)⟧)) := by
  let := probeSingle_finite (coefficientModule K 3) 0 2 (by decide)
  exact Module.Finite.equiv (homCoefficientsIso (probe K 3) (restrictedOutgoingIso K a)).symm.toLinearEquiv

theorem restrictedLeft_finrank : Module.finrank K
    (homCoefficients (probe K 3) (restrictedTriangle K a).obj₁) = 3 :=
  (homCoefficientsIso (probe K 3) (restrictedLeftIso K a)).toLinearEquiv.finrank_eq.trans
    (probe_coefficient_finrank 1 (by decide) (by decide))

theorem restrictedRight_finrank : Module.finrank K
    (homCoefficients (probe K 3) (restrictedTriangle K a).obj₃) = 3 :=
  (homCoefficientsIso (probe K 3) (restrictedRightIso K a)).toLinearEquiv.finrank_eq.trans
    (probe_coefficient_finrank 2 (by decide) (by decide))

theorem restrictedIncoming_finrank : Module.finrank K
    (homCoefficients (probe K 3) (restrictedTriangle K a).invRotate.obj₁) = 1 :=
  (homCoefficientsIso (probe K 3) (restrictedIncomingIso K a)).toLinearEquiv.finrank_eq.trans
    (probeEnd_finrank K 3)

theorem restrictedOutgoing_finrank : Module.finrank K
    (homCoefficients (probe K 3) (((restrictedTriangle K a).obj₁)⟦(1 : ℤ)⟧)) = 1 :=
  (homCoefficientsIso (probe K 3) (restrictedOutgoingIso K a)).toLinearEquiv.finrank_eq.trans
    (probeBottom_finrank K)

/-- Nonzero actual gluing is seen by the genuine outgoing representable map. -/
theorem restrictedOutgoing_nonzero (h : (restrictedTriangle K a).mor₃ ≠ 0) :
    postcompose (probe K 3) (restrictedTriangle K a).mor₃ ≠ 0 := by
  intro hz
  let T := restrictedTriangle K a
  let eR := restrictedRightIso K a
  let eL := (shiftFunctor (Derived K 3) (1 : ℤ)).mapIso (restrictedLeftIso K a)
  let f := eR.inv ≫ T.mor₃ ≫ eL.hom
  have hf : f = 0 := by
    apply probe_detects_connecting (coefficientModule K 3) (coefficientModule K 3)
      TrivialLayers.augmentationAction_coefficientModule TrivialLayers.augmentationAction_coefficientModule
      1 2 (by decide) (by decide) (by decide) f
    intro g
    have hh := congrArg (fun u : homCoefficients (probe K 3) T.obj₃ ⟶
      homCoefficients (probe K 3) (T.obj₁⟦(1 : ℤ)⟧) => u (g ≫ eR.inv)) hz
    change (g ≫ eR.inv) ≫ T.mor₃ = 0 at hh
    simpa only [f, Category.assoc, zero_comp] using congrArg (fun u => u ≫ eL.hom) hh
  apply h
  apply (cancel_epi eR.inv).mp
  apply (cancel_mono eL.hom).mp
  simpa only [f, Category.assoc, comp_zero, zero_comp] using hf

/-- The incoming boundary is the shifted negative of the same actual gluing. -/
theorem restrictedIncoming_zero_iff : (restrictedTriangle K a).invRotate.mor₁ = 0 ↔
    (restrictedTriangle K a).mor₃ = 0 := by
  let F := shiftFunctor (Derived K 3) (-1 : ℤ)
  let e := (shiftFunctorCompIsoId (Derived K 3) (1 : ℤ) (-1 : ℤ) (by norm_num)).app
    (restrictedTriangle K a).obj₁
  have hz : F.map (restrictedTriangle K a).mor₃ = 0 ↔ (restrictedTriangle K a).mor₃ = 0 := by
    constructor
    · intro h
      exact F.map_injective (by simpa using h)
    · intro h
      simp [h]
  convert (CategoryTheory.Preadditive.IsIso.comp_right_eq_zero
    (-(F.map (restrictedTriangle K a).mor₃)) e.hom).trans (neg_eq_zero.trans hz) using 1
  simp [Triangle.invRotate, F, e, CategoryTheory.Preadditive.neg_comp, shiftEquiv, shiftEquiv']

theorem restrictedIncoming_rank (h : (restrictedTriangle K a).mor₃ ≠ 0) :
    Module.finrank K (postcompose (probe K 3) (restrictedTriangle K a).invRotate.mor₁).hom.range = 1 := by
  apply rank_eq_one_of_domain _ ?_ (restrictedIncoming_finrank K a)
  exact postcompose_nonzero_of_sourceIso (probe K 3) (restrictedIncomingIso K a).symm _
    (fun hz => h ((restrictedIncoming_zero_iff K a).mp hz))

theorem restrictedOutgoing_rank (h : (restrictedTriangle K a).mor₃ ≠ 0) :
    Module.finrank K (postcompose (probe K 3) (restrictedTriangle K a).mor₃).hom.range = 1 :=
  rank_eq_one_of_codomain _ (restrictedOutgoing_nonzero K a h) (restrictedOutgoing_finrank K a)

/-- The actual represented native profile has six modes when the true
restriction class vanishes and exactly four otherwise. -/
theorem restrictedTriangle_count : Module.finrank K
    (homCoefficients (probe K 3) (restrictedTriangle K a).obj₂) =
      if (couplingClass K).mapExactFunctor (exampleRestriction K a) = 0 then 6 else 4 := by
  classical
  by_cases h : (couplingClass K).mapExactFunctor (exampleRestriction K a) = 0
  · rw [ite_eq_left h]
    have hδ := (restrictedConnecting_zero_iff K a).mpr h
    have hi := (restrictedIncoming_zero_iff K a).mpr hδ
    have he := triangle_dimension (probe K 3) (restrictedTriangle K a)
      (restrictedTriangle_distinguished K a)
    have hin : Module.finrank K
        (postcompose (probe K 3) (restrictedTriangle K a).invRotate.mor₁).hom.range = 0 := by
      have hz : postcompose (probe K 3) (restrictedTriangle K a).invRotate.mor₁ = 0 := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        change (show probe K 3 ⟶ _ from f) ≫ (restrictedTriangle K a).invRotate.mor₁ = 0
        rw [hi]
        simp
      rw [hz]
      simp
    have hout : Module.finrank K
        (postcompose (probe K 3) (restrictedTriangle K a).mor₃).hom.range = 0 := by
      have hz : postcompose (probe K 3) (restrictedTriangle K a).mor₃ = 0 := by
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro f
        change (show probe K 3 ⟶ _ from f) ≫ (restrictedTriangle K a).mor₃ = 0
        rw [hδ]
        simp
      rw [hz]
      simp
    rw [hin, hout, restrictedLeft_finrank, restrictedRight_finrank] at he
    omega
  · rw [ite_eq_right h]
    have hδ : (restrictedTriangle K a).mor₃ ≠ 0 :=
      fun hz => h ((restrictedConnecting_zero_iff K a).mp hz)
    exact triangle_count_four (probe K 3) (restrictedTriangle K a)
      (restrictedTriangle_distinguished K a) (restrictedLeft_finrank K a)
      (restrictedRight_finrank K a) (restrictedIncoming_rank K a hδ)
      (restrictedOutgoing_rank K a hδ)

end
end Decoupling.HighDim.Glued
