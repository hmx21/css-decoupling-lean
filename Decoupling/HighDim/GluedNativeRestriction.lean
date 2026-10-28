import Decoupling.HighDim.GluedNativeProfile
import Decoupling.HighDim.KoszulLatticeToric

/-!
# Restriction of the actual example's native gluing

The placed Koszul comparison is a genuine quasi-isomorphism. Its only
nonzero cochain component computes the same actual restriction as the
native Ext representative of the displayed coupling.
-/
namespace Decoupling.HighDim.Glued
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex Koszul KoszulLattice
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

/-- An augmentation-trivial target has no nonzero null-homotopic maps
from this actual placed Koszul resolution to the degree-one single. -/
theorem placed_map_zero_iff (A : ModuleCat (Laurent K 3))
    (hA : TrivialLayers.AugmentationAction A)
    (f : Toric.model K 3 3 ⟶ (CochainComplex.singleFunctor _ 1).obj A) :
    DerivedCategory.Q.map f = 0 ↔ f.f 1 = 0 := by
  let : (Toric.model K 3 3).IsKProjective :=
    CochainComplex.isKProjective_of_projective _ 3
  rw [ExtValuesFunctor.derived_eq_zero_iff_homotopy]
  constructor
  · rintro ⟨H⟩
    have hh := H.comm 1
    rw [dNext_eq H.hom (show (ComplexShape.up ℤ).Rel 1 2 from rfl),
      prevD_eq H.hom (show (ComplexShape.up ℤ).Rel 0 1 from rfl)] at hh
    have hd : ((CochainComplex.singleFunctor (ModuleCat (Laurent K 3)) 1).obj A).d 0 1 = 0 :=
      single_obj_d _ _ _ _ _
    simp only [hd, comp_zero, HomologicalComplex.zero_f, add_zero] at hh
    rw [hh]
    rw [show (Toric.model K 3 3).d 1 2 =
      (Toric.termIso K 3 3 2).hom ≫ boundary (Laurent K 3) (difference K) 1 ≫
        (Toric.termIso K 3 3 1).inv from Toric.differential K 3 3 1]
    rw [← cancel_mono (singleObjXSelf (.up ℤ) 1 A).hom]
    have hz := ExtValues.boundary_postcomp_zero A
      (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) 1
      ((Toric.termIso K 3 3 1).inv ≫ H.hom 2 1 ≫ (singleObjXSelf (.up ℤ) 1 A).hom)
    change boundary (Laurent K 3) (difference K) 1 ≫ _ = 0 at hz
    simp only [Category.assoc, hz, comp_zero, zero_comp]
  · intro h
    have hf : f = 0 := to_single_hom_ext h
    exact ⟨Homotopy.ofEq hf⟩

/-- The actual placed representative after the lattice comparison. -/
def restrictedCoupling (a : Translation 3 →+ Translation 3) :
    Toric.model K 3 3 ⟶
      (CochainComplex.singleFunctor _ 1).obj
        ((ModuleCat.restrictScalars (latticeMap K a)).obj (coefficientModule K 3)) :=
  latticeToricComparison K a 3 ≫
    ((ModuleCat.restrictScalars (latticeMap K a)).mapHomologicalComplex (.up ℤ)).map
      (couplingToSingle K) ≫
    ((ModuleCat.restrictScalars (latticeMap K a)).mapCochainComplexSingleFunctor 1).hom.app
      (coefficientModule K 3)

theorem restrictedCoupling_f_one (a : Translation 3 →+ Translation 3) :
    (restrictedCoupling K a).f 1 =
      (Toric.termIso K 3 3 2).hom ≫ (latticeComparison K a).f 2 ≫
        (ModuleCat.restrictScalars (latticeMap K a)).map (couplingCochain K) ≫
          (singleObjXSelf (.up ℤ) 1
            ((ModuleCat.restrictScalars (latticeMap K a)).obj (coefficientModule K 3))).inv := by
  simp only [restrictedCoupling, HomologicalComplex.comp_f,
    Functor.mapHomologicalComplex_map_f, couplingToSingle_f_one]
  have he := latticeToricComparison_f K a 3 2
  change (latticeToricComparison K a 3).f 1 = _ at he
  rw [he]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  simp [Functor.mapCochainComplexSingleFunctor]

theorem mapped_coupling_zero_iff (a : Translation 3 →+ Translation 3) :
    (ModuleCat.restrictScalars (latticeMap K a)).mapDerivedCategory.map
      (DerivedCategory.Q.map (couplingToSingle K)) = 0 ↔
    (couplingClass K).mapExactFunctor (ModuleCat.restrictScalars (latticeMap K a)) = 0 := by
  let F := ModuleCat.restrictScalars (latticeMap K a)
  have hFQ : F.mapDerivedCategory.map (DerivedCategory.Q.map (couplingToSingle K)) = 0 ↔
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (couplingToSingle K)) = 0 := by
    rw [← cancel_mono (F.mapDerivedCategoryFactors.hom.app _),
      F.mapDerivedCategoryFactors_hom_naturality]
    simp
  rw [hFQ]
  have hcomp : DerivedCategory.Q.map (restrictedCoupling K a) = 0 ↔
      DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map (couplingToSingle K)) = 0 := by
    simp only [restrictedCoupling, Functor.map_comp, IsIso.comp_left_eq_zero,
      IsIso.comp_right_eq_zero]
    rfl
  rw [← hcomp, placed_map_zero_iff K _
    (restrictedAugmentationAction K a _ (TrivialLayers.augmentationAction_coefficientModule (K := K) (D := 3))),
    restrictedCoupling_f_one]
  simp only [IsIso.comp_left_eq_zero]
  exact (coefficient_restriction_eq_zero_iff K a (coefficientModule K 3)
    (TrivialLayers.augmentationAction_coefficientModule (K := K) (D := 3)) 2 (couplingCochain K)).symm

end
end Decoupling.HighDim.Glued
