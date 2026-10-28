import Decoupling.HighDim.ExtValuesFunctor

/-!
# Exact-functor action on actual native Ext representatives

The augmentation square is required and proved for the lattice comparison;
it fixes the source transport, so this result computes values, not just kernels.
-/
namespace Decoupling.HighDim.ExtValuesFunctor
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.Preadditive
open KoszulExtFunctor
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard
variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
  [HasExt C] [HasExt D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X Y : C} (P : ProjectiveResolution X) {n : ℕ}
  (f : P.complex.X n ⟶ Y) (hf : P.complex.d (n+1) n ≫ f = 0)

/-- Pulling a native Ext class back to its actual projective resolution
gives its original cochain representative. -/
theorem extMk_hom_augmentation :
    DerivedCategory.Q.map P.π' ≫ (P.extMk f (n+1) rfl hf).hom =
      ShiftedHom.map (representative P f hf) DerivedCategory.Q := by
  rw [P.extMk_hom]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀,
    DerivedCategory.singleFunctorIsoCompQ, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, Iso.refl_inv, IsIso.hom_inv_id_assoc]
  erw [CategoryTheory.Functor.map_id]
  rw [Category.comp_id]
  rfl

/-- The mapped actual augmentation computes the full native image class. -/
theorem map_extMk_hom_augmentation :
    DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map P.π' ≫
      (F.mapCochainComplexSingleFunctor 0).hom.app X) ≫
        ((P.extMk f (n+1) rfl hf).mapExactFunctor F).hom =
      ShiftedHom.map ((F.mapHomologicalComplex (.up ℤ)).map (representative P f hf) ≫
        (mappedSingleIso (n := n) (Y := Y) F).hom) DerivedCategory.Q := by
  rw [Ext.mapExactFunctor_hom]
  simp only [Functor.map_comp, Category.assoc]
  rw [← F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app X]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc]
  have hn := F.mapDerivedCategoryFactors.inv.naturality P.π'
  dsimp only [Functor.comp_map] at hn
  erw [reassoc_of% hn]
  simp only [ShiftedHom.map, Category.assoc]
  rw [← Functor.map_comp_assoc, extMk_hom_augmentation]
  have hnat := ShiftedHom.map_naturality (representative P f hf) F.mapDerivedCategoryFactors.inv
  simp only [ShiftedHom.comp_mk₀, ShiftedHom.mk₀_comp, ShiftedHom.comp_map] at hnat
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc] at hnat ⊢
  erw [← reassoc_of% hnat]
  rw [← Functor.map_comp, F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app]
  simp only [mappedSingleIso, Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [DerivedCategory.Q.commShiftIso_hom_naturality]


/-- Full equality of the native image class with its computed cochain.
The actual augmentation square fixes the normalization of the source. -/
theorem map_extMk_eq_computed_extMk {Z : D} (Q : ProjectiveResolution Z)
    (ρ : Z ⟶ F.obj X)
    (χ : Q.cochainComplex ⟶ (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex)
    (hχ : χ ≫ (F.mapHomologicalComplex (.up ℤ)).map P.π' ≫
      (F.mapCochainComplexSingleFunctor 0).hom.app X =
        Q.π' ≫ (CochainComplex.singleFunctor D 0).map ρ)
    (g : Q.complex.X n ⟶ F.obj Y) (hg : Q.complex.d (n+1) n ≫ g = 0)
    (h : (Q.cochainComplexXIso (-n) n rfl).hom ≫ g =
      χ.f (-n) ≫ F.map ((P.cochainComplexXIso (-n) n rfl).hom ≫ f)) :
    (Ext.mk₀ ρ).comp ((P.extMk f (n+1) rfl hf).mapExactFunctor F) (zero_add n) =
      Q.extMk g (n+1) rfl hg := by
  apply Ext.homEquiv.injective
  change ((Ext.mk₀ ρ).comp _ _).hom = (Q.extMk g (n+1) rfl hg).hom
  rw [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp]
  apply (cancel_epi (DerivedCategory.Q.map Q.π')).mp
  rw [extMk_hom_augmentation]
  change DerivedCategory.Q.map Q.π' ≫ DerivedCategory.Q.map
    ((CochainComplex.singleFunctor D 0).map ρ) ≫ _ = _
  rw [← Functor.map_comp_assoc, ← hχ, Functor.map_comp,
    Category.assoc, map_extMk_hom_augmentation]
  have he := mapped_representative_eq F P f hf Q χ g hg h
  rw [← he]
  simp only [ShiftedHom.map, Functor.map_comp, Category.assoc]

end
end Decoupling.HighDim.ExtValuesFunctor
