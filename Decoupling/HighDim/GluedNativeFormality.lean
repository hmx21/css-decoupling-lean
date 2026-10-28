import Decoupling.HighDim.GluedNativeRestriction
import Decoupling.HighDim.TwoLayerRestriction

/-!
# Exact formality criterion for the literal six-qudit example

This criterion concerns the actual native profile of the concrete
checks. The proof retains the actual distinguished cone triangle and
uses the proved restriction formula for its displayed coupling.
-/
namespace Decoupling.HighDim.Glued
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Koszul KoszulLattice PostnikovTruncation
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

/-- The standard two coefficient layers, in their actual degrees. -/
def twoCoefficientLayers : DerivedCategory (ModuleCat (Laurent K 3)) :=
  (DerivedCategory.singleFunctor _ 1).obj (coefficientModule K 3) ⊞
    (DerivedCategory.singleFunctor _ 2).obj (coefficientModule K 3)

theorem couplingTriangle_mapped_zero_iff (a : Translation 3 →+ Translation 3) :
    (ModuleCat.restrictScalars (latticeMap K a)).mapDerivedCategory.map
      (couplingTriangle K).mor₃ = 0 ↔
    (couplingClass K).mapExactFunctor (ModuleCat.restrictScalars (latticeMap K a)) = 0 := by
  change (ModuleCat.restrictScalars (latticeMap K a)).mapDerivedCategory.map
    (-(DerivedCategory.Q.map (couplingToSingle K))⟦(1 : ℤ)⟧') = 0 ↔ _
  rw [Functor.map_neg, neg_eq_zero, ShiftedExt.map_shift_eq_zero_iff]
  exact mapped_coupling_zero_iff K a

/-- A complete native derived formality criterion for the actual displayed
matrices, on every integer lattice map, including negative and skew bases. -/
theorem actualProfile_formal_iff (a : Translation 3 →+ Translation 3) :
    Nonempty ((ModuleCat.restrictScalars (latticeMap K a)).mapDerivedCategory.obj
      (Profile.S_X (checks K)) ≅ twoCoefficientLayers K) ↔
    (couplingClass K).mapExactFunctor (ModuleCat.restrictScalars (latticeMap K a)) = 0 := by
  let F := ModuleCat.restrictScalars (latticeMap K a)
  let T := F.mapDerivedCategory.mapTriangle.obj (couplingTriangle K)
  let eL : T.obj₁ ≅ (DerivedCategory.singleFunctor _ 1).obj (coefficientModule K 3) :=
    F.mapDerivedCategory.mapIso (couplingTriangleLeftIso K) ≪≫
      (F.mapDerivedCategorySingleFunctor 1).app _ ≪≫
        (DerivedCategory.singleFunctor _ 1).mapIso (latticeCoefficientIso K a).symm
  let eR : T.obj₃ ≅ (DerivedCategory.singleFunctor _ 2).obj (coefficientModule K 3) :=
    F.mapDerivedCategory.mapIso (couplingTriangleRightIso K) ≪≫
      (F.mapDerivedCategorySingleFunctor 2).app _ ≪≫
        (DerivedCategory.singleFunctor _ 2).mapIso (latticeCoefficientIso K a).symm
  let : T.obj₁.IsLE (2 - 1) := t.isLE_of_iso eL.symm 1
  let : T.obj₃.IsGE 2 := t.isGE_of_iso eR.symm 2
  have hT := F.mapDerivedCategory.map_distinguished (couplingTriangle K)
    (couplingTriangle_distinguished K)
  have hs := TwoLayer.triangle_zero_iff_split T hT 2
  have hz : T.mor₃ = 0 ↔ F.mapDerivedCategory.map (couplingTriangle K).mor₃ = 0 := by
    change F.mapDerivedCategory.map (couplingTriangle K).mor₃ ≫ _ = 0 ↔ _
    exact CategoryTheory.Preadditive.IsIso.comp_right_eq_zero _ _
  rw [hz, couplingTriangle_mapped_zero_iff] at hs
  rw [hs]
  let eM : F.mapDerivedCategory.obj (Profile.S_X (checks K)) ≅ T.obj₂ :=
    F.mapDerivedCategory.mapIso (actualProfileConeIso K)
  constructor
  · rintro ⟨e⟩
    exact ⟨eM.symm ≪≫ e ≪≫ (biprod.mapIso eL eR).symm⟩
  · rintro ⟨e⟩
    exact ⟨eM ≪≫ e ≪≫ biprod.mapIso eL eR⟩

end
end Decoupling.HighDim.Glued
