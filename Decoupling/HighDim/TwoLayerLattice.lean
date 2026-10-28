import Decoupling.HighDim.ScalingLatticeChecksProfile
import Decoupling.HighDim.TrivialLayersCoordinates
import Decoupling.HighDim.ExactDerivedHomology
import Decoupling.HighDim.TwoLayerPhysical
import Decoupling.HighDim.ToricSplitLayers
import Decoupling.HighDim.ScalingSplitting

/-!
# Layer translation actions on the actual coarse-grained code

Source: necessity of Γ ⊆ Λ₀ in Corollary 2, HD008. Arbitrary finite-index
Γ is allowed initially. The equivalence below identifies its containment
in the genuine common kernel with augmentation action on the restricted
native layers, and relates those layers to the actual expanded checks.
-/

namespace Decoupling.HighDim.TwoLayer
open CategoryTheory ScalingLattice TrivialLayers
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [CommRing K] {D : ℕ}
  (Γ : AddSubgroup (Translation D)) (e : Γ ≃+ Translation D)

abbrev latticeRestriction : ModuleCat (Laurent K D) ⥤ ModuleCat (Laurent K D) :=
  ModuleCat.restrictScalars (coordinateEmbedding K Γ e)

theorem restricted_augmentation_iff (M : ModuleCat (Laurent K D)) :
    AugmentationAction ((latticeRestriction Γ e).obj M) ↔
      ∀ a : Γ, ∀ m : M, monomial K (a : Translation D) • m = m := by
  constructor
  · intro h a m
    have hh := h (monomial K (e a)) m
    change coordinateEmbedding K Γ e (monomial K (e a)) • m =
      coordinateEmbedding K Γ e (constant (augmentation (monomial K (e a)))) • m at hh
    simpa only [coordinateEmbedding_monomial, e.symm_apply_apply, augmentation_monomial,
      coordinateEmbedding_constant, map_one, one_smul] using hh
  · exact coordinate_augmentationAction Γ e M

variable {p q s r : ℕ} [Fact p.Prime]
  (c : CSS.Checks (ZMod p) D q s r)

theorem le_lambda0_iff_restricted_layers_augmentation :
    Γ ≤ Translations.lambda0 c ↔ ∀ j : ℕ, 1 ≤ j → j < D →
      AugmentationAction ((latticeRestriction Γ e).obj (Layers.layer c j)) := by
  constructor
  · intro h j hj hjD
    apply (restricted_augmentation_iff Γ e _).mpr
    intro a m
    exact (Translations.mem_lambda0_iff c a).mp (h a.property) j hj hjD m
  · intro h a ha
    apply (Translations.mem_lambda0_iff c a).mpr
    intro j hj hjD m
    exact (restricted_augmentation_iff Γ e _).mp (h j hj hjD) ⟨a, ha⟩ m

variable [Γ.FiniteIndex]

/-- Every positive layer of the actual coarse checks is the actual restricted layer. -/
def physicalLayerIso (n : ℕ) :
    Layers.layer (physicalChecks (ZMod p) Γ e c) (n + 1) ≅
      (latticeRestriction Γ e).obj (Layers.layer c (n + 1)) :=
  (Profile.homologyEquivLayer (physicalChecks (ZMod p) Γ e c) n).toModuleIso.symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat (Laurent (ZMod p) D)) (n + 1 : ℕ)).mapIso
      (physicalChecksRestrictionIso (ZMod p) Γ e c).symm ≪≫
    ExactDerivedHomology.homologyIso (latticeRestriction Γ e) (Profile.S_X c) (n + 1 : ℕ) ≪≫
    (latticeRestriction Γ e).mapIso (Profile.homologyEquivLayer c n).toModuleIso

/-- Every actual toric-stack decoupling forces the chosen lattice into
the full common kernel of the original superselection translations. -/
theorem le_lambda0_of_decouples {ι : Type} [Fintype ι] (forms : ι → ℕ)
    (hforms : ∀ i, forms i + 1 ≤ D)
    (hd : Toric.DecouplesToStack (ZMod p) D forms (physicalChecks (ZMod p) Γ e c)) :
    Γ ≤ Translations.lambda0 c := by
  obtain ⟨ep⟩ := Toric.profileIso_of_decouples forms (physicalChecks (ZMod p) Γ e c) hd
  let es := ep ≪≫ Toric.stackChecks_nativeProfileIso (ZMod p) D forms hforms
  apply (le_lambda0_iff_restricted_layers_augmentation Γ e c).mpr
  intro j hj _
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact ScalingSplitting.augmentationAction_of_iso (physicalLayerIso Γ e c n)
    (Toric.augmentationAction_of_nativeSplit (ZMod p) D forms
      (physicalChecks (ZMod p) Γ e c) es n)

end
end Decoupling.HighDim.TwoLayer
