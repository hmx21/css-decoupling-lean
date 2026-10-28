import Decoupling.HighDim.KoszulContractionAugmentation
import Decoupling.HighDim.ExtValuesFunctorExact
import Decoupling.HighDim.MinimalLatticeYoneda

/-!
# Identification of the contraction with the given native Ext class

HD010 Appendix B.3. The actual chain map has the given native class
because its composition with the target augmentation is exactly the
unique tensor representative. The comparison does not merely preserve
whether the class is zero.
-/

namespace Decoupling.HighDim.KoszulContraction
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.Preadditive
open Koszul TrivialLayers ExtValuesTensor CochainComplex.HomComplex
open KoszulExtFunctor ExtValuesFunctor
open scoped TensorProduct
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type} [Field K] {D : ℕ}
  (B A : ModuleCat (Laurent K D))
  [FiniteDimensional K (Layers.coefficients B)]
  [FiniteDimensional K (Layers.coefficients A)]
  (hB : AugmentationAction B) (hA : AugmentationAction A)

theorem tableMap_f_of_degree (n : ℕ)
    (f : Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A))
    (q k : ℕ) (hk : k = q + n) :
    (tableMap B A hB hA n f).f (-(k : ℤ)) =
      ((resolution B hB).cochainComplexXIso (-(k : ℤ)) k rfl).hom ≫
        ((tensorComplex B).XIsoOfEq hk).hom ≫ tableComponent B A hB n f q ≫
          ((resolution A hA).cochainComplexXIso (-(q : ℤ)) q rfl).inv ≫
            ((complex A hA).shiftFunctorObjXIso (n : ℤ)
              (-(k : ℤ)) (-(q : ℤ)) (by omega)).inv := by
  subst k
  simp only [HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom]
  erw [Category.id_comp]
  exact tableMap_f B A hB hA n f q

/-- Equality of actual cochain maps after augmentation. -/
theorem tableMap_augmentation (n : ℕ) (f : (tensorComplex B).X n ⟶ A) :
    tableMap B A hB hA n (tensorValues B A n f) ≫
      ((resolution A hA).π')⟦(n : ℤ)⟧' =
        representative (resolution B hB) f
          (tensor_boundary_postcomp_zero B A
            (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n f) := by
  apply HomologicalComplex.Hom.ext
  funext p
  by_cases hp : p = -(n : ℤ)
  · subst p
    simp only [HomologicalComplex.comp_f]
    rw [tableMap_f_of_degree B A hB hA n _ 0 n (Nat.zero_add n).symm]
    simp only [Category.assoc]
    erw [YonedaDetection.shift_component_naturality (resolution A hA).π'
      (n : ℤ) (-(n : ℤ)) 0 (by omega)]
    rw [(resolution A hA).π'_f_zero]
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_assoc]
    rw [representative_component]
    have haug := topComponent_augmentation B A hB hA n f
    change ((tensorComplex B).XIsoOfEq (Nat.zero_add n).symm).hom ≫
      tableComponent B A hB n (tensorValues B A n f) 0 ≫ (resolution A hA).π.f 0 = f at haug
    rw [reassoc_of% haug]
  · exact (IsZero.of_iso (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 A
      (p + n) (by omega))
      (((CochainComplex.singleFunctor (ModuleCat (Laurent K D)) 0).obj A).shiftFunctorObjXIso
        (n : ℤ) p (p + n) rfl)).eq_of_tgt _ _

/-- The explicit contraction associated to a genuine native Ext class. -/
def nativeMap (n : ℕ) (e : Ext B A n) : complex B hB ⟶ (complex A hA)⟦(n : ℤ)⟧ :=
  tableMap B A hB hA n (ExtValues.finiteExtEquiv B A hB hA n e)

/-- Native derived class identification, using the actual augmentations
of the two literal tensor Koszul resolutions. -/
theorem nativeMap_hom (n : ℕ) (e : Ext B A n) :
    DerivedCategory.Q.map (resolution B hB).π' ≫ e.hom =
      ShiftedHom.map (nativeMap B A hB hA n e ≫
        ((resolution A hA).π')⟦(n : ℤ)⟧') DerivedCategory.Q := by
  obtain ⟨f, rfl⟩ := tensorMk_surjective B A hB
    (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n e
  rw [nativeMap, finiteExtEquiv_tensorMk, tableMap_augmentation]
  exact extMk_hom_augmentation (resolution B hB) f
    (tensor_boundary_postcomp_zero B A
      (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n f)

/-- Native identification of the actual unshifted tensor resolution. -/
def derivedResolutionIso (M : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients M)] (hM : AugmentationAction M) :
    DerivedCategory.Q.obj (complex M hM) ≅
      (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) 0).obj M :=
  asIso (DerivedCategory.Q.map (resolution M hM).π')

/-- Native identification after the actual cochain shift. -/
def shiftedDerivedResolutionIso (M : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients M)] (hM : AugmentationAction M) (n : ℤ) :
    DerivedCategory.Q.obj ((complex M hM)⟦n⟧) ≅
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) 0).obj M)⟦n⟧ :=
  (DerivedCategory.Q.commShiftIso n).app (complex M hM) ≪≫
    (shiftFunctor _ n).mapIso (derivedResolutionIso M hM)

/-- The localized explicit contraction is exactly the original native
Ext morphism conjugated by the actual resolution identifications. -/
theorem nativeMap_Q (n : ℕ) (e : Ext B A n) :
    DerivedCategory.Q.map (nativeMap B A hB hA n e) =
      (derivedResolutionIso B hB).hom ≫ e.hom ≫
        (shiftedDerivedResolutionIso A hA (n : ℤ)).inv := by
  apply (cancel_mono (shiftedDerivedResolutionIso A hA (n : ℤ)).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change _ = DerivedCategory.Q.map (resolution B hB).π' ≫ e.hom
  rw [nativeMap_hom B A hB hA n e]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc,
    shiftedDerivedResolutionIso, Iso.trans_hom, Functor.mapIso_hom,
    derivedResolutionIso, asIso_hom]
  rw [DerivedCategory.Q.commShiftIso_hom_naturality]
  rfl

end
end Decoupling.HighDim.KoszulContraction
