import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Actual exact-functor restriction of Koszul Ext representatives

This generic interface uses mathlib's native derived Ext. A comparison is
an actual quasi-isomorphism of cochain complexes, and the vanishing hypothesis
is equality of actual chain morphisms. It will be supplied by the signed
Koszul comparison, not assumed in the final Laurent restriction theorem.
-/

namespace Decoupling.HighDim.KoszulExtFunctor

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open CochainComplex.HomComplex

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]
  [HasExt C] [HasExt D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  {X Y : C} (P : ProjectiveResolution X) {n : ℕ}
  (f : P.complex.X n ⟶ Y) (hf : P.complex.d (n + 1) n ≫ f = 0)

/-- The actual cochain morphism representing a native `extMk` class. -/
def representative :
    P.cochainComplex ⟶ ((CochainComplex.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧ :=
  Cocycle.equivHomShift.symm
    (Cocycle.toSingleMk ((P.cochainComplexXIso (-n) n rfl).hom ≫ f) (by simp)
      (-((n + 1 : ℕ) : ℤ)) (by omega)
      (by rw [P.cochainComplex_d (-((n + 1 : ℕ) : ℤ)) (-n) (n + 1) n rfl rfl]
          simp [Category.assoc, hf]))

omit [HasExt C] in
theorem representative_f (i : ℤ) :
    (representative P f hf).f i =
      (Cochain.toSingleMk ((P.cochainComplexXIso (-n) n rfl).hom ≫ f) (by simp)).v
        i (i + n) rfl ≫
      (((CochainComplex.singleFunctor C 0).obj Y).shiftFunctorObjXIso (n : ℤ) i
        (i + n) rfl).inv := by
  simp only [representative, Cocycle.equivHomShift_symm_apply, Cocycle.homOf,
    Cocycle.rightShift_coe, Cochain.rightShift_v, Cocycle.toSingleMk_coe]

omit [HasExt C] in
theorem representative_f_ne (i : ℤ) (hi : i ≠ -(n : ℤ)) :
    (representative P f hf).f i = 0 := by
  rw [representative_f, Cochain.toSingleMk_v_eq_zero _ _ _ _ _ hi]
  simp

/-- If the mapped cocycle becomes zero after a genuine quasi-isomorphism,
then its image under native derived `Ext.mapExactFunctor` is zero. -/
theorem map_extMk_eq_zero_of_comparison
    {Q : CochainComplex D ℤ}
    (χ : Q ⟶ (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex)
    [QuasiIso χ]
    (hχ : χ ≫ (F.mapHomologicalComplex (.up ℤ)).map (representative P f hf) = 0) :
    (P.extMk f (n + 1) rfl hf).mapExactFunctor F = 0 := by
  let g := representative P f hf
  have hQ : DerivedCategory.Q.map ((F.mapHomologicalComplex (.up ℤ)).map g) = 0 := by
    rw [← cancel_epi (DerivedCategory.Q.map χ), ← Functor.map_comp, hχ]
    simp
  have hFQ : F.mapDerivedCategory.map (DerivedCategory.Q.map g) = 0 := by
    rw [← cancel_mono (F.mapDerivedCategoryFactors.hom.app _)]
    rw [F.mapDerivedCategoryFactors_hom_naturality]
    simp only [hQ, comp_zero, zero_comp]
  have hg : (ShiftedHom.map g DerivedCategory.Q).map F.mapDerivedCategory = 0 := by
    simp only [ShiftedHom.map, Functor.map_comp, hFQ, zero_comp]
  ext
  rw [Ext.mapExactFunctor_hom, Ext.zero_hom, P.extMk_hom]
  simp only [ShiftedHom.map_comp]
  change (F.mapDerivedCategorySingleFunctor 0).inv.app X ≫
    ((ShiftedHom.mk₀ _ rfl _).map F.mapDerivedCategory).comp
      (((ShiftedHom.map g DerivedCategory.Q).map F.mapDerivedCategory).comp
        ((ShiftedHom.mk₀ _ rfl _).map F.mapDerivedCategory) (zero_add _)) (add_zero _) ≫ _ = 0
  simp only [hg, ShiftedHom.zero_comp, ShiftedHom.comp_zero, zero_comp, comp_zero]

/-- It suffices to check the single nonzero component of the actual cocycle. -/
theorem map_extMk_eq_zero_of_component
    {Q : CochainComplex D ℤ}
    (χ : Q ⟶ (F.mapHomologicalComplex (.up ℤ)).obj P.cochainComplex)
    [QuasiIso χ]
    (hχ : χ.f (-(n : ℤ)) ≫ F.map ((P.cochainComplexXIso (-n) n rfl).hom ≫ f) = 0) :
    (P.extMk f (n + 1) rfl hf).mapExactFunctor F = 0 := by
  apply map_extMk_eq_zero_of_comparison F P f hf χ
  ext i
  by_cases hi : i = -(n : ℤ)
  · subst i
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      representative, Cocycle.equivHomShift_symm_apply, Cocycle.homOf,
      Cocycle.rightShift_coe, Cocycle.toSingleMk_coe, HomologicalComplex.zero_f]
    rw [Cochain.rightShift_v _ _ _ _ _ _ _ 0 (by omega),
      Cochain.toSingleMk_v, Functor.map_comp, Functor.map_comp]
    simp only [← Category.assoc, hχ, zero_comp]
  · simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      representative_f_ne P f hf i hi, F.map_zero, comp_zero, HomologicalComplex.zero_f]

end
end Decoupling.HighDim.KoszulExtFunctor
