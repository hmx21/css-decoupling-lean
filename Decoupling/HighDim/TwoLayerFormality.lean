import Decoupling.HighDim.TwoLayerRestriction
import Decoupling.HighDim.ToricSplitConnecting

/-!
# The zero-, one-, and two-layer formality criteria

Source: Corollary 2, HD008. Empty and singleton support are proved
separately; two genuine layers have exactly the canonical Ext attachment.
-/

namespace Decoupling.HighDim.TwoLayer
open CategoryTheory CategoryTheory.Limits PostnikovInduction FiniteBiproduct
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {R S : Type} [CommRing R] [CommRing S]

abbrev homologySum (X : DerivedCategory (ModuleCat R)) (s : Finset ℤ) :=
  sumObj (fun i => (DerivedCategory.singleFunctor (ModuleCat R) i).obj (H X i)) s

def homologySumIso {X Y : DerivedCategory (ModuleCat R)} (e : X ≅ Y) (s : Finset ℤ) :
    homologySum X s ≅ homologySum Y s :=
  biproduct.mapIso (fun i => (DerivedCategory.singleFunctor (ModuleCat R) i).mapIso
    ((DerivedCategory.homologyFunctor (ModuleCat R) i).mapIso e))

theorem formal_iff_of_iso {X Y : DerivedCategory (ModuleCat R)} (e : X ≅ Y) (s : Finset ℤ) :
    Nonempty (X ≅ homologySum X s) ↔ Nonempty (Y ≅ homologySum Y s) :=
  ⟨fun ⟨f⟩ => ⟨e.symm ≪≫ f ≪≫ homologySumIso e s⟩,
    fun ⟨f⟩ => ⟨e ≪≫ f ≪≫ (homologySumIso e s).symm⟩⟩

def pairSumIso (X : DerivedCategory (ModuleCat R)) (i j : ℤ) (hij : i ≠ j) :
    homologySum X {i, j} ≅
      (DerivedCategory.singleFunctor (ModuleCat R) i).obj (H X i) ⊞
        (DerivedCategory.singleFunctor (ModuleCat R) j).obj (H X j) := by
  let B := fun k => (DerivedCategory.singleFunctor (ModuleCat R) k).obj (H X k)
  have he : ({i, j} : Finset ℤ).erase j = {i} := by ext k; simp; omega
  exact (eraseIso B {i, j} j (by simp)).symm ≪≫ biprod.mapIso
    (eqToIso (congrArg (sumObj B) he) ≪≫ singletonIso B i) (Iso.refl _)

theorem formal_of_card_le_one (X : DerivedCategory (ModuleCat R)) (s : Finset ℤ)
    (hX : Supported X s) (hs : s.card ≤ 1) : Nonempty (X ≅ homologySum X s) := by
  by_cases he : s = ∅
  · subst s
    let : X.IsLE 0 := supported_isLE hX 0 (by simp)
    let : X.IsGE 1 := supported_isGE hX 1 (by simp)
    have hzero : IsZero X := DerivedCategory.TStructure.t.isZero X 0 1
    have hsum : IsZero (homologySum X ∅) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply biproduct.hom_ext
      intro i
      exact (Finset.notMem_empty _ i.property).elim
    exact ⟨hzero.isoZero ≪≫ hsum.isoZero.symm⟩
  · have hc : s.card = 1 := by have := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr he); omega
    obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hc
    let : X.IsLE i := supported_isLE hX i (by simp)
    let : X.IsGE i := supported_isGE hX i (by simp)
    exact ⟨Profile.singleDegreeIso X i ≪≫ (singletonIso
      (fun k => (DerivedCategory.singleFunctor (ModuleCat R) k).obj (H X k)) i).symm⟩

theorem formal_pair_iff_connecting (X : DerivedCategory (ModuleCat R))
    (i j : ℤ) (hij : i < j) (hX : Supported X {i, j}) :
    Nonempty (X ≅ homologySum X {i, j}) ↔ connecting X j = 0 := by
  rw [← layerConnecting_eq_zero_iff X i j hij hX, layerConnecting_zero_iff_split]
  exact ⟨fun ⟨e⟩ => ⟨e ≪≫ pairSumIso X i j (by omega)⟩,
    fun ⟨e⟩ => ⟨e ≪≫ (pairSumIso X i j (by omega)).symm⟩⟩

theorem connecting_zero_of_formal (X : DerivedCategory (ModuleCat R)) (s : Finset ℤ)
    (h : Nonempty (X ≅ homologySum X s)) (j : ℤ) : connecting X j = 0 := by
  obtain ⟨e⟩ := h
  exact PostnikovTruncation.connecting_of_iso e j
    (PostnikovTruncation.connecting_biproduct _ j
      (fun i => PostnikovTruncation.connecting_single _ i j))

theorem formal_iff_all_connecting (X : DerivedCategory (ModuleCat R)) (s : Finset ℤ)
    (hX : Supported X s) (hs : s.card ≤ 2) :
    Nonempty (X ≅ homologySum X s) ↔ ∀ j, connecting X j = 0 := by
  constructor
  · exact fun h => connecting_zero_of_formal X s h
  · intro h
    by_cases hsmall : s.card ≤ 1
    · exact formal_of_card_le_one X s hX hsmall
    · obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp (by omega : s.card = 2)
      rcases lt_or_gt_of_ne hij with hij | hij
      · exact (formal_pair_iff_connecting X i j hij hX).mpr (h j)
      · rw [Finset.pair_comm] at hX ⊢
        exact (formal_pair_iff_connecting X j i hij hX).mpr (h i)

theorem nativeGluing_map_zero_iff_formal (X : DerivedCategory (ModuleCat R))
    (i j : ℤ) (hij : i < j) (hX : Supported X {i, j})
    (F : ModuleCat R ⥤ ModuleCat S) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    (nativeGluing X i j hij hX).mapExactFunctor F = 0 ↔
      Nonempty (F.mapDerivedCategory.obj X ≅ homologySum (F.mapDerivedCategory.obj X) {i, j}) := by
  rw [nativeGluing_map_zero_iff_split]
  let e := pairSumIso (F.mapDerivedCategory.obj X) i j (by omega) ≪≫
    biprod.mapIso
      ((DerivedCategory.singleFunctor (ModuleCat S) i).mapIso (ExactDerivedHomology.homologyIso F X i))
      ((DerivedCategory.singleFunctor (ModuleCat S) j).mapIso (ExactDerivedHomology.homologyIso F X j))
  exact ⟨fun ⟨f⟩ => ⟨f ≪≫ e.symm⟩, fun ⟨f⟩ => ⟨f ≪≫ e⟩⟩

end
end Decoupling.HighDim.TwoLayer
