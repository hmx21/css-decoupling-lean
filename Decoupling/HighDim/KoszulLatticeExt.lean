import Decoupling.HighDim.KoszulLatticeRestriction
import Decoupling.HighDim.ExtValuesFunctor

/-!
# Native Ext restriction and arbitrary-lattice minors

Source: Appendix B.2. This module connects the constructed lattice
comparison to the actual native exact-functor action on derived Ext.
-/

namespace Decoupling.HighDim.KoszulLattice

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
open Koszul ExtValues TrivialLayers
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] {D : ℕ}

def latticeCochainComparison (a : Translation D →+ Translation D) :
    (projectiveResolution K D).cochainComplex ⟶
      ((ModuleCat.restrictScalars (latticeMap K a)).mapHomologicalComplex (.up ℤ)).obj
        (projectiveResolution K D).cochainComplex :=
  HomologicalComplex.extendMap (latticeComparison K a) ComplexShape.embeddingDownNat ≫
    (KoszulExtendFunctor.iso (ModuleCat.restrictScalars (latticeMap K a))
      (laurentComplex K D)).inv

instance latticeCochainComparison_quasiIso (a : Translation D →+ Translation D) :
    QuasiIso (latticeCochainComparison K a) := by
  dsimp [latticeCochainComparison]
  infer_instance

theorem latticeCochainComparison_f (a : Translation D →+ Translation D) (n : ℕ) :
    (latticeCochainComparison K a).f (-(n : ℤ)) =
      ((projectiveResolution K D).cochainComplexXIso (-n) n rfl).hom ≫
      (latticeComparison K a).f n ≫
      (ModuleCat.restrictScalars (latticeMap K a)).map
        ((projectiveResolution K D).cochainComplexXIso (-n) n rfl).inv := by
  change (HomologicalComplex.extendMap (latticeComparison K a) ComplexShape.embeddingDownNat ≫
    (KoszulExtendFunctor.iso (ModuleCat.restrictScalars (latticeMap K a))
      (laurentComplex K D)).inv).f (-(n : ℤ)) = _
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.extendMap_f _ _ (i := n) (i' := -(n : ℤ)) rfl]
  simp only [KoszulExtendFunctor.iso, HomologicalComplex.Hom.isoOfComponents_inv_f,
    KoszulExtendFunctor.termIso_nat, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

theorem restrictedAugmentationAction (a : Translation D →+ Translation D)
    (A : ModuleCat (Laurent K D)) (hA : AugmentationAction A) :
    AugmentationAction ((ModuleCat.restrictScalars (latticeMap K a)).obj A) := by
  intro r x
  change latticeMap K a r • (show A from x) =
    latticeMap K a (constant (augmentation r)) • (show A from x)
  rw [hA, augmentation_latticeMap, latticeMap_constant]

/-- Both directions of the native restriction criterion on actual
cochains. No representative or comparison-existence hypothesis remains. -/
theorem coefficient_restriction_eq_zero_iff (a : Translation D →+ Translation D)
    (A : ModuleCat (Laurent K D)) (hA : AugmentationAction A) (n : ℕ)
    (f : (laurentComplex K D).X n ⟶ A) :
    (coefficientMk A (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA)
      n f).mapExactFunctor (ModuleCat.restrictScalars (latticeMap K a)) = 0 ↔
      (latticeComparison K a).f n ≫
        (ModuleCat.restrictScalars (latticeMap K a)).map f = 0 := by
  let F := ModuleCat.restrictScalars (latticeMap K a)
  let g := (latticeComparison K a).f n ≫ F.map f
  have hFA := ExtRestrictionVanishing.difference_annihilates_of_augmentationAction
    (F.obj A) (restrictedAugmentationAction K a A hA)
  have h := ExtValuesFunctor.map_extMk_eq_zero_iff_computed_extMk F
    (projectiveResolution K D) f (boundary_postcomp_zero A
      (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n f)
    (projectiveResolution K D) (latticeCochainComparison K a) g
      (boundary_postcomp_zero (F.obj A) hFA n g) (by
        rw [latticeCochainComparison_f]
        simp only [g, F, Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc])
  change ((projectiveResolution K D).extMk f (n + 1) rfl
    (boundary_postcomp_zero A
      (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n f)).mapExactFunctor F = 0 ↔ g = 0
  rw [h]
  change coefficientMk (F.obj A) hFA n g = 0 ↔ g = 0
  exact (AddEquiv.ofBijective (coefficientMk (F.obj A) hFA n)
    ⟨coefficientMk_injective (F.obj A) hFA n, coefficientMk_surjective (F.obj A) hFA n⟩).map_eq_zero_iff

/-- The representative of the actual restriction has the stated minors
as its ordered-cell values, including signs and negative integer entries. -/
theorem restricted_cochain_values (a : Translation D →+ Translation D)
    (A : ModuleCat (Laurent K D)) (hA : AugmentationAction A) (n : ℕ)
    (f : (laurentComplex K D).X n ⟶ A) (J : Cell D n) :
    (show Layers.coefficients A from
      (((latticeComparison K a).f n ≫
        (ModuleCat.restrictScalars (latticeMap K a)).map f) (Finsupp.single J 1))) =
      ∑ I : Cell D n, Matrix.det (fun k l => (a (translationBasis (J k)) (I l) : K)) •
        (show Layers.coefficients A from f (Finsupp.single I 1)) := by
  change (show Layers.coefficients A from f ((latticeComparison K a).f n (Finsupp.single J 1))) = _
  rw [cochain_apply_eq_sum A hA]
  apply Finset.sum_congr rfl
  intro I _
  rw [augmentation_latticeComparison_single]

/-- The explicit minors criterion for the genuine native Ext restriction
of a coefficient-source class. -/
theorem coefficient_restriction_eq_zero_iff_minors (a : Translation D →+ Translation D)
    (A : ModuleCat (Laurent K D)) (hA : AugmentationAction A) (n : ℕ)
    (e : Ext (coefficientModule K D) A n) :
    e.mapExactFunctor (ModuleCat.restrictScalars (latticeMap K a)) = 0 ↔
      ∀ J : Cell D n,
        (∑ I : Cell D n, Matrix.det (fun k l => (a (translationBasis (J k)) (I l) : K)) •
          (show Layers.coefficients A from coefficientTableEquiv A
            (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n e I)) = 0 := by
  obtain ⟨f, rfl⟩ := coefficientMk_surjective A
    (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n e
  rw [coefficient_restriction_eq_zero_iff K a A hA n f]
  simp only [coefficientTableEquiv_mk]
  constructor
  · intro h J
    rw [← restricted_cochain_values K a A hA n f J, h]
    rfl
  · intro h
    apply ModuleCat.hom_ext
    apply (Finsupp.basisSingleOne : Module.Basis (Cell D n) (Laurent K D)
      (Term (Laurent K D) D n)).ext
    intro J
    exact (restricted_cochain_values K a A hA n f J).trans (h J)

end
end Decoupling.HighDim.KoszulLattice
