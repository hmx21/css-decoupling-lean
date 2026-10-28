import Decoupling.HighDim.TwoLayerExt

/-!
# Exact restriction of the canonical two-layer native Ext class

Source: Corollary 2, HD008. For every exact functor (in particular actual
lattice scalar restriction), the native gluing class maps to zero iff the
mapped profile is the direct sum of its two mapped homology layers.
No vanishing lemma or formality hypothesis is assumed.
-/

namespace Decoupling.HighDim.TwoLayer
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Abelian
open PostnikovTruncation PostnikovInduction
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {R S : Type} [CommRing R] [CommRing S]
  (X : DerivedCategory (ModuleCat R)) (i j : ℤ) (hij : i < j)
  (hX : Supported X {i, j})

/-- The actual Ext^(j-i+1) attachment of the two genuine homology modules. -/
def nativeGluing : Ext (H X j) (H X i) (j - i + 1).toNat :=
  extOfConnecting i j (j - i + 1).toNat (Int.toNat_of_nonneg (by omega))
    (layerConnecting X i j hij hX)

variable (F : ModuleCat R ⥤ ModuleCat S) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

theorem nativeGluing_map_zero_iff_connecting :
    (nativeGluing X i j hij hX).mapExactFunctor F = 0 ↔
      F.mapDerivedCategory.map (connecting X j) = 0 := by
  rw [nativeGluing, extOfConnecting_map_zero_iff]
  simp only [layerConnecting, Functor.map_comp]
  constructor
  · intro h
    apply (cancel_epi (F.mapDerivedCategory.map (upperLayerIso X i j hij hX).inv)).mp
    apply (cancel_mono
      (F.mapDerivedCategory.map ((lowerLayerIso X i j hij hX).hom⟦(1 : ℤ)⟧'))).mp
    simpa only [Category.assoc, comp_zero, zero_comp] using h
  · intro h
    rw [h, zero_comp, comp_zero]

theorem mapped_connecting_zero_iff_split :
    F.mapDerivedCategory.map (connecting X j) = 0 ↔
      Nonempty (F.mapDerivedCategory.obj X ≅
        F.mapDerivedCategory.obj (lower X j) ⊞ F.mapDerivedCategory.obj (upper X j)) := by
  let T := F.mapDerivedCategory.mapTriangle.obj (triangle X j)
  let : T.obj₁.IsLE (j - 1) := ExactDerivedHomology.isLE F (lower X j) (j - 1)
  let : T.obj₃.IsGE j := ExactDerivedHomology.isGE F (upper X j) j
  have hT := F.mapDerivedCategory.map_distinguished (triangle X j) (t.triangleLTGE_distinguished j X)
  have he := triangle_zero_iff_split T hT j
  have hz : T.mor₃ = 0 ↔ F.mapDerivedCategory.map (connecting X j) = 0 := by
    change F.mapDerivedCategory.map (connecting X j) ≫ _ = 0 ↔ _
    constructor
    · intro h
      exact (cancel_mono ((F.mapDerivedCategory.commShiftIso (1 : ℤ)).hom.app (lower X j))).mp
        (by simpa using h)
    · intro h
      rw [h, zero_comp]
  exact hz.symm.trans he

/-- The complete native Ext restriction/formality equivalence for two layers. -/
theorem nativeGluing_map_zero_iff_split :
    (nativeGluing X i j hij hX).mapExactFunctor F = 0 ↔
      Nonempty (F.mapDerivedCategory.obj X ≅
        (DerivedCategory.singleFunctor (ModuleCat S) i).obj (F.obj (H X i)) ⊞
          (DerivedCategory.singleFunctor (ModuleCat S) j).obj (F.obj (H X j))) := by
  rw [nativeGluing_map_zero_iff_connecting, mapped_connecting_zero_iff_split]
  let el := F.mapDerivedCategory.mapIso (lowerLayerIso X i j hij hX) ≪≫
    (F.mapDerivedCategorySingleFunctor i).app (H X i)
  let eu := F.mapDerivedCategory.mapIso (upperLayerIso X i j hij hX) ≪≫
    (F.mapDerivedCategorySingleFunctor j).app (H X j)
  constructor
  · rintro ⟨e⟩
    exact ⟨e ≪≫ biprod.mapIso el eu⟩
  · rintro ⟨e⟩
    exact ⟨e ≪≫ (biprod.mapIso el eu).symm⟩

end
end Decoupling.HighDim.TwoLayer
