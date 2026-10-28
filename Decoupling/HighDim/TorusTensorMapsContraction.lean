import Decoupling.HighDim.TorusTensorMapsFinite
import Decoupling.HighDim.PerfectModelBasic
import Decoupling.HighDim.KoszulContractionNative
import Decoupling.HighDim.KoszulContractionBounds
import Decoupling.HighDim.TwoLayerExt

/-!
# Arbitrary actual connecting components induce the explicit contraction

HD010 Appendix B.3. The class is obtained from the given derived
connecting component, then transported back using genuine shift
equivalences. The map on H⁰ is the actual lift-then-tensor map.
-/
namespace Decoupling.HighDim.Torus
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] {D : ℕ}

theorem TensorModel.shift_lift_spec {X Y : Derived.{0} K D}
    (M : TensorModel X) (N : TensorModel Y) (f : X ⟶ Y)
    (g : M.complex ⟶ N.complex)
    (hg : DerivedCategory.Q.map g = M.iso.hom ≫ f ≫ N.iso.inv) (a : ℤ) :
    DerivedCategory.Q.map (g⟦a⟧') =
      (PerfectModel.shift M a).iso.hom ≫ f⟦a⟧' ≫ (PerfectModel.shift N a).iso.inv := by
  apply (cancel_mono (PerfectModel.shift N a).iso.hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  change DerivedCategory.Q.map (g⟦a⟧') ≫
    (DerivedCategory.Q.commShiftIso a).hom.app N.complex ≫ N.iso.hom⟦a⟧' =
    ((DerivedCategory.Q.commShiftIso a).hom.app M.complex ≫ M.iso.hom⟦a⟧') ≫ f⟦a⟧'
  rw [DerivedCategory.Q.commShiftIso_hom_naturality_assoc]
  rw [hg]
  simp only [Category.assoc, ← Functor.map_comp,
    Iso.inv_hom_id, Category.comp_id]

namespace Contraction
open KoszulContraction TrivialLayers
variable (B A : ModuleCat (Laurent K D))
  [FiniteDimensional K (Layers.coefficients B)] [FiniteDimensional K (Layers.coefficients A)]
  (hB : AugmentationAction B) (hA : AugmentationAction A)

def resolutionModel (M : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients M)] (hM : AugmentationAction M) :
    TensorModel ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) 0).obj M) where
  complex := KoszulContraction.complex M hM
  lower := -(D : ℤ)
  upper := 0
  finite := fun _ => inferInstance
  free := fun _ => inferInstance
  boundedBelow := inferInstance
  boundedAbove := inferInstance
  iso := derivedResolutionIso M hM

theorem native_tensor_map (n : ℕ) (κ : Ext B A n) :
    TensorModel.map (resolutionModel B hB) (PerfectModel.shift (resolutionModel A hA) n) κ.hom =
      tensorH0Map (nativeMap B A hB hA n κ) := by
  apply TensorModel.map_eq_of_lift
  exact nativeMap_Q B A hB hA n κ

variable (i j : ℤ) (n : ℕ) (hn : (n : ℤ) = j - i + 1)

def targetNormalization :
    (((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj A)⟦(1 : ℤ)⟧)⟦j⟧ ≅
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) 0).obj A)⟦(n : ℤ)⟧ :=
  (shiftFunctor (Derived.{0} K D) j).mapIso (TwoLayer.connectingTargetIso A i) ≪≫
    TwoLayer.shiftedTargetIso A i j n hn

def normalizedSourceModel :
    TensorModel (((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj B)⟦j⟧) :=
  PerfectModel.ofIso (resolutionModel B hB) (TwoLayer.shiftedSourceIso B j).symm

def normalizedTargetModel :
    TensorModel ((((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj A)⟦(1 : ℤ)⟧)⟦j⟧) :=
  PerfectModel.ofIso (PerfectModel.shift (resolutionModel A hA) (n : ℤ))
    (targetNormalization A i j n hn).symm

def sourceModel : TensorModel ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj B) :=
  PerfectModel.ofIso (PerfectModel.shift (normalizedSourceModel B hB j) (-j))
    ((shiftFunctorCompIsoId (Derived.{0} K D) j (-j) (add_neg_cancel j)).app _)

def targetModel :
    TensorModel (((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj A)⟦(1 : ℤ)⟧) :=
  PerfectModel.ofIso (PerfectModel.shift (normalizedTargetModel A hA i j n hn) (-j))
    ((shiftFunctorCompIsoId (Derived.{0} K D) j (-j) (add_neg_cancel j)).app _)

variable (δ : (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj B ⟶
  ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj A)⟦(1 : ℤ)⟧)

/-- The actual tensor Koszul contraction, placed in the original degrees.
Its Ext class is extracted from δ itself, not supplied independently. -/
def connectingContraction : (sourceModel B hB j).complex ⟶ (targetModel A hA i j n hn).complex :=
  (nativeMap B A hB hA n (TwoLayer.extOfConnecting i j n hn δ))⟦(-j)⟧'

theorem normalizedContraction_Q :
    DerivedCategory.Q.map (nativeMap B A hB hA n (TwoLayer.extOfConnecting i j n hn δ)) =
      (normalizedSourceModel B hB j).iso.hom ≫ δ⟦j⟧' ≫
        (normalizedTargetModel A hA i j n hn).iso.inv := by
  rw [nativeMap_Q]
  simp only [TwoLayer.extOfConnecting, Ext.hom, Equiv.apply_symm_apply, Functor.map_comp,
    normalizedSourceModel, normalizedTargetModel, PerfectModel.ofIso, PerfectModel.shift,
    resolutionModel, targetNormalization, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Functor.mapIso_hom, Category.assoc]
  rfl

/-- The actual shifted chain map represents the original connecting
component with all endpoint and shift identifications retained. -/
theorem connectingContraction_Q :
    DerivedCategory.Q.map (connectingContraction B A hB hA i j n hn δ) =
      (sourceModel B hB j).iso.hom ≫ δ ≫ (targetModel A hA i j n hn).iso.inv := by
  have he := TensorModel.shift_lift_spec (normalizedSourceModel B hB j)
    (normalizedTargetModel A hA i j n hn) (δ⟦j⟧')
    (nativeMap B A hB hA n (TwoLayer.extOfConnecting i j n hn δ))
    (normalizedContraction_Q B A hB hA i j n hn δ) (-j)
  change DerivedCategory.Q.map (connectingContraction B A hB hA i j n hn δ) = _ at he
  rw [he]
  dsimp only [sourceModel, targetModel, PerfectModel.ofIso, Iso.trans_hom, Iso.trans_inv]
  simp only [Category.assoc]
  congr 1
  have hnδ := (shiftFunctorCompIsoId (Derived.{0} K D) j (-j) (add_neg_cancel j)).hom.naturality δ
  dsimp only [Functor.comp_map, Functor.id_map] at hnδ
  erw [← reassoc_of% hnδ]
  simp

/-- The required actual δ_* identification. The left side is obtained
by a genuine derived lift and scalar extension; the right side uses
the explicit signed Hom-valued contraction chain map. -/
theorem connecting_tensor_map :
    TensorModel.map (sourceModel B hB j) (targetModel A hA i j n hn) δ =
      tensorH0Map (connectingContraction B A hB hA i j n hn δ) :=
  TensorModel.map_eq_of_lift _ _ δ _ (connectingContraction_Q B A hB hA i j n hn δ)

/-- The same equality on any chosen models, in particular the canonical
models used in B1. Both comparisons are actual tensor-induced maps. -/
theorem connecting_tensor_map_any_models
    (M : TensorModel ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj B))
    (N : TensorModel (((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj A)⟦(1 : ℤ)⟧)) :
    TensorModel.map M N δ =
      (TensorModel.comparison M (sourceModel B hB j)).hom ≫
        tensorH0Map (connectingContraction B A hB hA i j n hn δ) ≫
          (TensorModel.comparison (targetModel A hA i j n hn) N).hom := by
  rw [← connecting_tensor_map B A hB hA i j n hn δ]
  change TensorModel.map M N δ = TensorModel.map M (sourceModel B hB j) (𝟙 _) ≫
    TensorModel.map (sourceModel B hB j) (targetModel A hA i j n hn) δ ≫
      TensorModel.map (targetModel A hA i j n hn) N (𝟙 _)
  rw [← TensorModel.map_comp, ← TensorModel.map_comp, Category.id_comp, Category.comp_id]

end Contraction
end
end Decoupling.HighDim.Torus
