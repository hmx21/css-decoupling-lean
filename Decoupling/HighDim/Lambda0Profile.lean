import Decoupling.HighDim.ScalingSplitting
import Decoupling.HighDim.ProfileSupport
import Decoupling.HighDim.TrivialLayersCoordinates

/-!
# The actual CSS profile on its common translation kernel

This discharges the augmentation and finite-homology hypotheses of the
Postnikov theorem from the paper's original hypotheses. Layer dimensions
are those before restriction. The only topological input is the actual
two-sided CSS condition; no splitting is supplied.
-/

namespace Decoupling.HighDim.Lambda0Profile

open CategoryTheory CategoryTheory.Limits TrivialLayers PostnikovInduction
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {p D q s r : ℕ} [Fact p.Prime]
  (c : CSS.Checks (ZMod p) D q s r) (h : Layers.FiniteXLayers c)

instance restriction_additive : (lambda0Restriction c h).Additive := by
  unfold lambda0Restriction
  infer_instance

instance restriction_preservesFiniteLimits : PreservesFiniteLimits (lambda0Restriction c h) := by
  unfold lambda0Restriction
  infer_instance

instance restriction_preservesFiniteColimits : PreservesFiniteColimits (lambda0Restriction c h) := by
  unfold lambda0Restriction
  infer_instance

def profile := (lambda0Restriction c h).mapDerivedCategory.obj (Profile.S_X c)

def homologyLayerIso (n : ℕ) : H (profile c h) (n + 1 : ℕ) ≅
    (lambda0Restriction c h).obj (Layers.layer c (n + 1)) :=
  ExactDerivedHomology.homologyIso (lambda0Restriction c h) (Profile.S_X c) (n + 1 : ℕ) ≪≫
    (lambda0Restriction c h).mapIso (Profile.homologyEquivLayer c n).toModuleIso

theorem supported (hc : c.Topological) (hD : 1 ≤ D) :
    Supported (profile c h) (Profile.support c) := by
  intro i hi
  exact ((lambda0Restriction c h).map_isZero
    (Profile.homology_isZero_outside_support c hc hD i hi)).of_iso
      (ExactDerivedHomology.homologyIso (lambda0Restriction c h) (Profile.S_X c) i)

theorem restrictedLayer_trivialFinite (j : ℕ) (hj : 1 ≤ j) (hjD : j < D) :
    ScalingSplitting.TrivialFinite ((lambda0Restriction c h).obj (Layers.layer c j)) := by
  have := h j hj hjD
  refine ⟨coordinate_augmentationAction (Translations.lambda0 c) (lambda0Coordinates c h)
    (Layers.layer c j) (fun a m => (Translations.mem_lambda0_iff c a).mp a.property j hj hjD m), ?_⟩
  exact Module.Finite.equiv
    (coefficientRestrictionEquiv (Translations.lambda0 c) (lambda0Coordinates c h) (Layers.layer c j)).symm

theorem homology_trivialFinite (i : ℤ) (hi : i ∈ Profile.support c) :
    ScalingSplitting.TrivialFinite (H (profile c h) i) := by
  obtain ⟨n, hn, hnD, _, rfl⟩ := (Profile.mem_support_iff c i).mp hi
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  exact ScalingSplitting.trivialFinite_of_iso (homologyLayerIso c h n).symm
    (restrictedLayer_trivialFinite c h (n + 1) hn hnD)

def homologyCoordinatesIso (j : ℕ) (hj : 1 ≤ j) (hjD : j < D) :
    H (profile c h) (j : ℤ) ≅ coefficientVector (ZMod p) D (Layers.multiplicity c j) := by
  cases j with
  | zero => omega
  | succ n => exact homologyLayerIso c h n ≪≫ lambda0_coordinate_layerIso c h (n + 1) hj hjD

theorem exists_split (hc : c.Topological) (hD : 1 ≤ D) :
    Nonempty ((ExactIteration.derived (ScalingSplitting.restriction p)
      (Layers.nonzeroLayerCount c - 1)).obj (profile c h) ≅
      FiniteBiproduct.sumObj
        (fun i => (DerivedCategory.singleFunctor (ModuleCat (Laurent (ZMod p) D)) i).obj
          (H (profile c h) i)) (Profile.support c)) := by
  have he := ScalingSplitting.exists_split_including_empty p (Profile.support c)
    (profile c h) (supported c h hc hD) (homology_trivialFinite c h)
  simpa only [Profile.support_card] using he

end
end Decoupling.HighDim.Lambda0Profile
