import Decoupling.HighDim.KoszulExtFunctor
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Detecting native exact-functor restriction on actual representatives

Generic derived-category bookkeeping for Appendix B.2. These lemmas
refer to the native localization and native `Ext.mapExactFunctor`.
-/

namespace Decoupling.HighDim.ExtValuesFunctor

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.Preadditive
open CochainComplex.HomComplex KoszulExtFunctor
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

/-- For a genuinely K-projective source, vanishing after the native derived
localization is exactly null-homotopy of the original chain map. -/
theorem derived_eq_zero_iff_homotopy {C : Type*} [Category* C] [Abelian C]
    {P L : CochainComplex C ℤ} [P.IsKProjective] (g : P ⟶ L) :
    DerivedCategory.Q.map g = 0 ↔ Nonempty (Homotopy g 0) := by
  rw [← HomotopyCategory.quotient_map_eq_zero_iff]
  constructor
  · intro h
    apply (CochainComplex.IsKProjective.Qh_map_bijective P _).injective
    rw [Functor.map_zero, ← cancel_mono ((DerivedCategory.quotientCompQhIso C).hom.app L),
      DerivedCategory.quotientCompQhIso_hom_naturality]
    simp [h]
  · intro h
    rw [← cancel_epi ((DerivedCategory.quotientCompQhIso C).hom.app P),
      ← DerivedCategory.quotientCompQhIso_hom_naturality, h]
    simp

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
  [HasExt C] [HasExt D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X Y : C} (P : ProjectiveResolution X) {n : ℕ}
  (f : P.complex.X n ⟶ Y) (hf : P.complex.d (n + 1) n ≫ f = 0)

theorem map_extMk_eq_zero_iff_map_representative :
    (P.extMk f (n + 1) rfl hf).mapExactFunctor F = 0 ↔
      DerivedCategory.Q.map
        ((F.mapHomologicalComplex (.up ℤ)).map (representative P f hf)) = 0 := by
  have he : (P.extMk f (n + 1) rfl hf).mapExactFunctor F = 0 ↔
      ((P.extMk f (n + 1) rfl hf).mapExactFunctor F).hom = 0 := by
    constructor
    · intro h; simp [h]
    · intro h; apply Ext.ext; simpa using h
  rw [he, Ext.mapExactFunctor_hom, P.extMk_hom]
  simp only [ShiftedHom.mk₀_comp,
    ShiftedHom.comp_mk₀, Functor.map_comp, ShiftedHom.map]
  simp only [Category.assoc, IsIso.comp_left_eq_zero, IsIso.comp_right_eq_zero]
  change F.mapDerivedCategory.map (DerivedCategory.Q.map (representative P f hf)) = 0 ↔ _
  constructor
  · intro hFQ
    rw [← cancel_mono (F.mapDerivedCategoryFactors.hom.app _)] at hFQ
    rw [F.mapDerivedCategoryFactors_hom_naturality] at hFQ
    simpa using hFQ
  · intro h
    have hFQ : F.mapDerivedCategory.map (DerivedCategory.Q.map (representative P f hf)) = 0 := by
      rw [← cancel_mono (F.mapDerivedCategoryFactors.hom.app _),
        F.mapDerivedCategoryFactors_hom_naturality]
      simp [h]
    exact hFQ

/-- Vanishing of a native class is detected by its actual localized
projective-resolution representative. -/
theorem extMk_eq_zero_iff_representative :
    P.extMk f (n + 1) rfl hf = 0 ↔
      DerivedCategory.Q.map (representative P f hf) = 0 := by
  have he : P.extMk f (n + 1) rfl hf = 0 ↔
      (P.extMk f (n + 1) rfl hf).hom = 0 := by
    constructor
    · intro h; simp [h]
    · intro h; apply Ext.ext; simpa using h
  rw [he, P.extMk_hom]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ShiftedHom.map,
    Category.assoc, IsIso.comp_left_eq_zero, IsIso.comp_right_eq_zero]
  rfl

/-- A constructed projective comparison detects actual Ext restriction
through null-homotopy, in both directions. -/
theorem map_extMk_eq_zero_iff_comparison_homotopy
    {Q : CochainComplex D ℤ} [Q.IsKProjective]
    (χ : Q ⟶ (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex)
    [QuasiIso χ] :
    (P.extMk f (n + 1) rfl hf).mapExactFunctor F = 0 ↔
      Nonempty (Homotopy
        (χ ≫ (F.mapHomologicalComplex (.up ℤ)).map (representative P f hf)) 0) := by
  rw [map_extMk_eq_zero_iff_map_representative,
    ← derived_eq_zero_iff_homotopy, Functor.map_comp, IsIso.comp_left_eq_zero]

omit [HasExt C] in
/-- Normalize the only nonzero component of an actual Ext representative. -/
theorem representative_component :
    (representative P f hf).f (-(n : ℤ)) =
      (P.cochainComplexXIso (-n) n rfl).hom ≫ f ≫
        (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).inv ≫
          (((CochainComplex.singleFunctor C 0).obj Y).shiftFunctorObjXIso (n : ℤ)
            (-n) 0 (by omega)).inv := by
  simp only [representative, Cocycle.equivHomShift_symm_apply, Cocycle.homOf,
    Cocycle.rightShift_coe, Cocycle.toSingleMk_coe]
  rw [Cochain.rightShift_v _ _ _ _ _ _ _ 0 (by omega), Cochain.toSingleMk_v]
  simp only [Category.assoc]

/-- The canonical transport of the mapped shifted single complex. -/
def mappedSingleIso :
    (F.mapHomologicalComplex (.up ℤ)).obj (((CochainComplex.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) ≅
      ((CochainComplex.singleFunctor D 0).obj (F.obj Y))⟦(n : ℤ)⟧ :=
  ((F.mapHomologicalComplex (.up ℤ)).commShiftIso (n : ℤ)).app
      ((CochainComplex.singleFunctor C 0).obj Y) ≪≫
    (shiftFunctor _ (n : ℤ)).mapIso ((F.mapCochainComplexSingleFunctor 0).app Y)

omit [HasExt C] [HasExt D] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
theorem mappedSingle_component (i : ℤ) (hi : i = 0) :
    F.map (HomologicalComplex.singleObjXSelf (.up ℤ) 0 Y).inv ≫
      F.map (((CochainComplex.singleFunctor C 0).obj Y).XIsoOfEq hi).inv ≫
        ((HomologicalComplex.singleMapHomologicalComplex F (.up ℤ) 0).hom.app Y).f i =
      (HomologicalComplex.singleObjXSelf (.up ℤ) 0 (F.obj Y)).inv ≫
        (((CochainComplex.singleFunctor D 0).obj (F.obj Y)).XIsoOfEq hi).inv := by
  subst i
  simp [← Functor.map_comp_assoc]

omit [HasExt C] [HasExt D] [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- Equality of actual cochain representatives after the exact functor,
reduced to the one component containing the cochain. -/
theorem mapped_representative_eq {Z : D} (Q : ProjectiveResolution Z)
    (χ : Q.cochainComplex ⟶ (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex)
    (g : Q.complex.X n ⟶ F.obj Y) (hg : Q.complex.d (n + 1) n ≫ g = 0)
    (h : (Q.cochainComplexXIso (-n) n rfl).hom ≫ g =
      χ.f (-n) ≫ F.map ((P.cochainComplexXIso (-n) n rfl).hom ≫ f)) :
    χ ≫ (F.mapHomologicalComplex (.up ℤ)).map (representative P f hf) ≫
      (mappedSingleIso (n := n) (Y := Y) F).hom = representative Q g hg := by
  ext i
  by_cases hi : i = -(n : ℤ)
  · subst i
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      representative_component, mappedSingleIso, Iso.trans_hom,
      Iso.app_hom, Functor.mapIso_hom, HomologicalComplex.comp_f,
      Functor.mapHomologicalComplex_commShiftIso_hom_app_f,
      Functor.map_comp]
    rw [reassoc_of% h]
    simp only [Functor.map_comp, Category.assoc]
    congr 3
    simp only [CochainComplex.shiftFunctorObjXIso, CochainComplex.shiftFunctor_map_f',
      Functor.mapCochainComplexSingleFunctor]
    dsimp only [Functor.comp_obj, Functor.mapHomologicalComplex_obj_X,
      CochainComplex.shiftFunctor_obj_X']
    rw [Category.id_comp]
    exact mappedSingle_component (Y := Y) F (-(n : ℤ) + n) (by omega)
  · simp [representative_f_ne P f hf i hi, representative_f_ne Q g hg i hi]

/-- The actual exact-functor restriction vanishes exactly when its computed
cochain, regarded through the genuine target projective resolution, does.
The comparison must be a proved quasi-isomorphism. -/
theorem map_extMk_eq_zero_iff_computed_extMk {Z : D} (Q : ProjectiveResolution Z)
    (χ : Q.cochainComplex ⟶ (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex)
    [QuasiIso χ]
    (g : Q.complex.X n ⟶ F.obj Y) (hg : Q.complex.d (n + 1) n ≫ g = 0)
    (h : (Q.cochainComplexXIso (-n) n rfl).hom ≫ g =
      χ.f (-n) ≫ F.map ((P.cochainComplexXIso (-n) n rfl).hom ≫ f)) :
    (P.extMk f (n + 1) rfl hf).mapExactFunctor F = 0 ↔
      Q.extMk g (n + 1) rfl hg = 0 := by
  rw [map_extMk_eq_zero_iff_map_representative,
    extMk_eq_zero_iff_representative]
  have he := congrArg DerivedCategory.Q.map (mapped_representative_eq F P f hf Q χ g hg h)
  rw [Functor.map_comp, Functor.map_comp] at he
  rw [← he, IsIso.comp_left_eq_zero, IsIso.comp_right_eq_zero]

end
end Decoupling.HighDim.ExtValuesFunctor
