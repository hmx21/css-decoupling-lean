import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.CategoryTheory.Abelian.Ext

/-!
# Actual Ext restriction controls morphisms between shifted layers

This is the degree bookkeeping for the Postnikov connecting components.
The vanishing premise is the map on native derived Ext induced by the
exact functor, not a statement about a replacement vector space.
-/

namespace Decoupling.HighDim.ShiftedExt

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
noncomputable section
attribute [local instance] HasDerivedCategory.standard

variable {C : Type*} [Category* C] [Abelian C] {D : Type*} [Category* D] [Abelian D]
  [HasExt C] [HasExt D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

theorem map_hom_eq_zero {A B : C} {n : ℕ} (e : Ext A B n)
    (h : e.mapExactFunctor F = 0) : F.mapDerivedCategory.map e.hom = 0 := by
  have hh := congrArg Ext.hom h
  rw [Ext.mapExactFunctor_hom, Ext.zero_hom] at hh
  simpa [ShiftedHom.map] using hh

omit [HasExt C] [HasExt D] in
theorem map_shift_eq_zero_iff {X Y : DerivedCategory C} (f : X ⟶ Y) (a : ℤ) :
    F.mapDerivedCategory.map (f⟦a⟧') = 0 ↔ F.mapDerivedCategory.map f = 0 := by
  constructor
  · intro h
    apply (shiftFunctor (DerivedCategory D) a).map_injective
    have hn := F.mapDerivedCategory.commShiftIso_hom_naturality f a
    rw [h, zero_comp] at hn
    have hz : (F.mapDerivedCategory.map f)⟦a⟧' = 0 :=
      (cancel_epi ((F.mapDerivedCategory.commShiftIso a).hom.app X)).mp (by simpa using hn.symm)
    simpa using hz
  · intro h
    have hn := F.mapDerivedCategory.commShiftIso_hom_naturality f a
    rw [h, Functor.map_zero, comp_zero] at hn
    exact (cancel_mono ((F.mapDerivedCategory.commShiftIso a).hom.app Y)).mp (by simpa using hn)

/-- A map between layers in degrees `a` and `b` is an actual Ext class of
degree `a-b`; the formula is used only with the displayed nonnegative degree. -/
theorem map_between_singles_eq_zero {A B : C} (a b : ℤ) (n : ℕ)
    (hn : (n : ℤ) + b = a)
    (h : ∀ e : Ext A B n, e.mapExactFunctor F = 0)
    (f : (DerivedCategory.singleFunctor C a).obj A ⟶
      (DerivedCategory.singleFunctor C b).obj B) : F.mapDerivedCategory.map f = 0 := by
  let eA : ((DerivedCategory.singleFunctor C a).obj A)⟦a⟧ ≅
      (DerivedCategory.singleFunctor C 0).obj A :=
    ((DerivedCategory.singleFunctors C).shiftIso a 0 a (by simp)).app A
  let eB : ((DerivedCategory.singleFunctor C b).obj B)⟦a⟧ ≅
      ((DerivedCategory.singleFunctor C 0).obj B)⟦(n : ℤ)⟧ :=
    ((DerivedCategory.singleFunctors C).shiftIso a (-(n : ℤ)) b (by omega)).app B ≪≫
      (((DerivedCategory.singleFunctors C).shiftIso (n : ℤ) (-(n : ℤ)) 0
        (by omega)).app B).symm
  let g := eA.inv ≫ f⟦a⟧' ≫ eB.hom
  let e : Ext A B n := Ext.homEquiv.symm g
  have hg : F.mapDerivedCategory.map g = 0 := by
    simpa only [e, Ext.hom, Equiv.apply_symm_apply] using map_hom_eq_zero F e (h e)
  apply (map_shift_eq_zero_iff F f a).mp
  have hg' : F.mapDerivedCategory.map eA.inv ≫
      F.mapDerivedCategory.map (f⟦a⟧') ≫ F.mapDerivedCategory.map eB.hom = 0 := by
    simpa only [g, Functor.map_comp] using hg
  have hh := (cancel_epi (F.mapDerivedCategory.map eA.inv)).mp
    (show _ = F.mapDerivedCategory.map eA.inv ≫ 0 by simpa using hg')
  exact (cancel_mono (F.mapDerivedCategory.map eB.hom)).mp (by simpa using hh)

/-- The Postnikov component from degree `j` to degree `i` shifted by one
has Ext degree `j-i+1`, with the sign convention of the actual derived shift. -/
theorem map_connecting_component_eq_zero {A B : C} (i j : ℤ) (n : ℕ)
    (hn : (n : ℤ) = j - i + 1)
    (h : ∀ e : Ext A B n, e.mapExactFunctor F = 0)
    (f : (DerivedCategory.singleFunctor C j).obj A ⟶
      ((DerivedCategory.singleFunctor C i).obj B)⟦(1 : ℤ)⟧) :
    F.mapDerivedCategory.map f = 0 := by
  let eB : ((DerivedCategory.singleFunctor C i).obj B)⟦(1 : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor C (i - 1)).obj B :=
    ((DerivedCategory.singleFunctors C).shiftIso 1 (i - 1) i (by omega)).app B
  have hh := map_between_singles_eq_zero F j (i - 1) n (by omega) h (f ≫ eB.hom)
  exact (cancel_mono (F.mapDerivedCategory.map eB.hom)).mp
    (by simpa only [Functor.map_comp, zero_comp] using hh)

end
end Decoupling.HighDim.ShiftedExt
