import Decoupling.HighDim.KoszulLatticeExt
import Decoupling.HighDim.ExtValuesFunctorExact

/-!
# Full native restriction values, with the actual source normalization

The comparison covers the identity-on-elements coefficient isomorphism.
Consequently the normalized native image class equals the computed
cochain class, and its full ordered table is the signed minors formula.
-/
namespace Decoupling.HighDim.KoszulLattice
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex Koszul ExtValues TrivialLayers
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] {D : ℕ}

theorem latticeCochainComparison_augmentation (a : Translation D →+ Translation D) :
    latticeCochainComparison K a ≫
      ((ModuleCat.restrictScalars (latticeMap K a)).mapHomologicalComplex (.up ℤ)).map
        (projectiveResolution K D).π' ≫
      ((ModuleCat.restrictScalars (latticeMap K a)).mapCochainComplexSingleFunctor 0).hom.app
        (coefficientModule K D) =
    (projectiveResolution K D).π' ≫
      (CochainComplex.singleFunctor (ModuleCat (Laurent K D)) 0).map
        (latticeCoefficientIso K a).hom := by
  apply HomologicalComplex.to_single_hom_ext
  simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    ProjectiveResolution.π'_f_zero]
  have he := latticeCochainComparison_f K a 0
  change (latticeCochainComparison K a).f 0 = _ at he
  rw [he]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc]
  erw [Iso.inv_hom_id]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]
  have hpi : (projectiveResolution K D).π.f 0 = augmentationMap K D := rfl
  rw [hpi]
  rw [← Category.assoc ((latticeComparison K a).f 0), latticeComparison_augmentation_zero]
  simp [Functor.mapCochainComplexSingleFunctor, CochainComplex.singleFunctor, single_map_f_self,
    ← Functor.map_comp_assoc]

/-- Native restriction with the canonical identity-on-elements source
coefficient identification. -/
def coefficientRestriction (a : Translation D →+ Translation D)
    (A : ModuleCat (Laurent K D)) (n : ℕ) (e : Ext (coefficientModule K D) A n) :
    Ext (coefficientModule K D)
      ((ModuleCat.restrictScalars (latticeMap K a)).obj A) n :=
  (Ext.mk₀ (latticeCoefficientIso K a).hom).comp
    (e.mapExactFunctor (ModuleCat.restrictScalars (latticeMap K a))) (zero_add n)

theorem coefficientRestriction_mk (a : Translation D →+ Translation D)
    (A : ModuleCat (Laurent K D)) (hA : AugmentationAction A) (n : ℕ)
    (f : (laurentComplex K D).X n ⟶ A) :
    coefficientRestriction K a A n (coefficientMk A
      (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n f) =
    coefficientMk ((ModuleCat.restrictScalars (latticeMap K a)).obj A)
      (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction _
        (restrictedAugmentationAction K a A hA)) n
      ((latticeComparison K a).f n ≫ (ModuleCat.restrictScalars (latticeMap K a)).map f) := by
  exact ExtValuesFunctor.map_extMk_eq_computed_extMk
    (ModuleCat.restrictScalars (latticeMap K a)) (projectiveResolution K D) f
      (boundary_postcomp_zero A
        (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n f)
    (projectiveResolution K D) (latticeCoefficientIso K a).hom (latticeCochainComparison K a)
      (latticeCochainComparison_augmentation K a) _ (boundary_postcomp_zero _
        (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction _
          (restrictedAugmentationAction K a A hA)) n _) (by
        rw [latticeCochainComparison_f]
        simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc])

/-- Every table entry of the actual normalized restriction equals the
signed integer-minors combination of the original native table. -/
theorem coefficientRestriction_table (a : Translation D →+ Translation D)
    (A : ModuleCat (Laurent K D)) (hA : AugmentationAction A) (n : ℕ)
    (e : Ext (coefficientModule K D) A n) (J : Cell D n) :
    (show Layers.coefficients A from
      coefficientTableEquiv ((ModuleCat.restrictScalars (latticeMap K a)).obj A)
        (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction _
          (restrictedAugmentationAction K a A hA)) n (coefficientRestriction K a A n e) J) =
    ∑ I : Cell D n, Matrix.det (fun k l => (a (translationBasis (J k)) (I l) : K)) •
      (show Layers.coefficients A from coefficientTableEquiv A
        (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n e I) := by
  obtain ⟨f, rfl⟩ := coefficientMk_surjective A
    (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n e
  rw [coefficientRestriction_mk K a A hA n f, coefficientTableEquiv_mk]
  simp only [coefficientTableEquiv_mk]
  exact restricted_cochain_values K a A hA n f J

end
end Decoupling.HighDim.KoszulLattice
