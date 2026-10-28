import Decoupling.HighDim.TwoLayerPostnikov
import Decoupling.HighDim.ExactDerivedHomology

/-!
# The native Ext class of a canonical two-layer gluing

Source: Corollary 2 and equation (attachments), HD008. The class below
is constructed from the canonical connecting morphism using mathlib's
actual Ext–derived-Hom equivalence. Its restriction is the actual
`Ext.mapExactFunctor`, with vanishing equivalent to that of the mapped
connecting morphism.
-/

namespace Decoupling.HighDim.TwoLayer
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {R S : Type} [CommRing R] [CommRing S]

def shiftedSourceIso (A : ModuleCat R) (j : ℤ) :
    ((DerivedCategory.singleFunctor (ModuleCat R) j).obj A)⟦j⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat R) 0).obj A :=
  ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso j 0 j (by omega)).app A

def shiftedTargetIso (B : ModuleCat R) (i j : ℤ) (n : ℕ) (hn : (n : ℤ) = j - i + 1) :
    ((DerivedCategory.singleFunctor (ModuleCat R) (i - 1)).obj B)⟦j⟧ ≅
      ((DerivedCategory.singleFunctor (ModuleCat R) 0).obj B)⟦(n : ℤ)⟧ :=
  ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso j (-(n : ℤ)) (i - 1)
    (by omega)).app B ≪≫
    (((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso (n : ℤ) (-(n : ℤ)) 0
      (by omega)).app B).symm

def connectingTargetIso (B : ModuleCat R) (i : ℤ) :
    ((DerivedCategory.singleFunctor (ModuleCat R) i).obj B)⟦(1 : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat R) (i - 1)).obj B :=
  ((DerivedCategory.singleFunctors (ModuleCat R)).shiftIso 1 (i - 1) i (by omega)).app B

/-- A degree-correct native Ext class associated to a map between shifted layers. -/
def extOfConnecting {A B : ModuleCat R} (i j : ℤ) (n : ℕ)
    (hn : (n : ℤ) = j - i + 1)
    (f : (DerivedCategory.singleFunctor (ModuleCat R) j).obj A ⟶
      ((DerivedCategory.singleFunctor (ModuleCat R) i).obj B)⟦(1 : ℤ)⟧) : Ext A B n :=
  Ext.homEquiv.symm ((shiftedSourceIso A j).inv ≫
    (f ≫ (connectingTargetIso B i).hom)⟦j⟧' ≫ (shiftedTargetIso B i j n hn).hom)

variable (F : ModuleCat R ⥤ ModuleCat S) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

theorem mapExt_zero_iff {A B : ModuleCat R} {n : ℕ} (e : Ext A B n) :
    e.mapExactFunctor F = 0 ↔ F.mapDerivedCategory.map e.hom = 0 := by
  constructor
  · exact ShiftedExt.map_hom_eq_zero F e
  · intro h
    apply Ext.homEquiv.injective
    change (e.mapExactFunctor F).hom = (0 : Ext (F.obj A) (F.obj B) n).hom
    rw [Ext.mapExactFunctor_hom, Ext.zero_hom]
    simp [ShiftedHom.map, h]

theorem extOfConnecting_map_zero_iff {A B : ModuleCat R} (i j : ℤ) (n : ℕ)
    (hn : (n : ℤ) = j - i + 1)
    (f : (DerivedCategory.singleFunctor (ModuleCat R) j).obj A ⟶
      ((DerivedCategory.singleFunctor (ModuleCat R) i).obj B)⟦(1 : ℤ)⟧) :
    (extOfConnecting i j n hn f).mapExactFunctor F = 0 ↔ F.mapDerivedCategory.map f = 0 := by
  rw [mapExt_zero_iff]
  simp only [extOfConnecting, Ext.hom, Equiv.apply_symm_apply]
  constructor
  · intro h
    have h' : F.mapDerivedCategory.map ((f ≫ (connectingTargetIso B i).hom)⟦j⟧') = 0 := by
      apply (cancel_epi (F.mapDerivedCategory.map (shiftedSourceIso A j).inv)).mp
      apply (cancel_mono (F.mapDerivedCategory.map (shiftedTargetIso B i j n hn).hom)).mp
      simpa only [Functor.map_comp, Category.assoc, zero_comp, comp_zero] using h
    have h'' := (ShiftedExt.map_shift_eq_zero_iff F _ j).mp h'
    apply (cancel_mono (F.mapDerivedCategory.map (connectingTargetIso B i).hom)).mp
    simpa only [Functor.map_comp, zero_comp] using h''
  · intro h
    have h' : F.mapDerivedCategory.map (f ≫ (connectingTargetIso B i).hom) = 0 := by
      rw [Functor.map_comp, h, zero_comp]
    have h'' := (ShiftedExt.map_shift_eq_zero_iff F _ j).mpr h'
    rw [Functor.map_comp, Functor.map_comp, h'', zero_comp, comp_zero]

end
end Decoupling.HighDim.TwoLayer
