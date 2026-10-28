import Decoupling.HighDim.ScalingLattice

/-! # Common-kernel Ext layers in genuine standard Laurent coordinates -/

namespace Decoupling.HighDim.TrivialLayers

open CategoryTheory LatticeRestriction ScalingLattice
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [CommRing K] {D : ℕ}
  (Λ : AddSubgroup (Translation D)) (e : Λ ≃+ Translation D)
  (M : ModuleCat (Laurent K D))

/-- Restriction and a lattice basis do not change the coefficient vector space. -/
def coefficientRestrictionEquiv :
    Layers.coefficients ((ModuleCat.restrictScalars (coordinateEmbedding K Λ e)).obj M) ≃ₗ[K]
      Layers.coefficients M where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a m := by
    change coordinateEmbedding K Λ e (constant a) • (show M from m) = constant (D := D) a • (show M from m)
    rw [coordinateEmbedding_constant]

theorem coefficient_finrank [StrongRankCondition K] :
    Module.finrank K
      (Layers.coefficients ((ModuleCat.restrictScalars (coordinateEmbedding K Λ e)).obj M)) =
        Module.finrank K (Layers.coefficients M) :=
  (coefficientRestrictionEquiv Λ e M).finrank_eq

/-- The standard-coordinate Laurent action is augmentation whenever the
actual retained monomials fix the original module. -/
theorem coordinate_augmentationAction
    (h : ∀ a : Λ, ∀ m : M, monomial K (a : Translation D) • m = m) :
    AugmentationAction ((ModuleCat.restrictScalars (coordinateEmbedding K Λ e)).obj M) := by
  intro a m
  change coordinateEmbedding K Λ e a • (show M from m) =
    coordinateEmbedding K Λ e (constant (augmentation a)) • (show M from m)
  rw [coordinateEmbedding_constant]
  have hh := scalar_action_of_fixed Λ M h ((ringCoordinates K Λ e).symm a) (show M from m)
  change coordinateEmbedding K Λ e a • (show M from m) =
    constant (D := D) (augmentation (coordinateEmbedding K Λ e a)) • (show M from m) at hh
  simpa only [augmentation_coordinateEmbedding] using hh

/-- Actual restriction, identified with the original coefficient space
carrying augmentation action, by the identity on underlying elements. -/
def coordinateCoefficientEquiv
    (h : ∀ a : Λ, ∀ m : M, monomial K (a : Translation D) • m = m) :
    (ModuleCat.restrictScalars (coordinateEmbedding K Λ e)).obj M ≃ₗ[Laurent K D]
      coefficientObject (D := D) (Layers.coefficients M) where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a m := by
    have hh := coordinate_augmentationAction Λ e M h a m
    change coordinateEmbedding K Λ e a • (show M from m) =
      coordinateEmbedding K Λ e (constant (augmentation a)) • (show M from m) at hh
    change coordinateEmbedding K Λ e a • (show M from m) =
      constant (D := D) (augmentation a) • (show M from m)
    simpa only [coordinateEmbedding_constant] using hh

section Lambda0

variable {p q s r : ℕ} [Fact p.Prime]
  (c : CSS.Checks (ZMod p) D q s r)
  (h : Layers.FiniteXLayers c)

/-- The finite-index instance is obtained from the original finite Ext layers. -/
def lambda0Coordinates : Translations.lambda0 c ≃+ Translation D := by
  letI := Translations.lambda0_finiteIndex c h
  exact LatticeBasis.coordinates (Translations.lambda0 c)

def lambda0Restriction : ModuleCat (Laurent (ZMod p) D) ⥤ ModuleCat (Laurent (ZMod p) D) :=
  ModuleCat.restrictScalars
    (coordinateEmbedding (ZMod p) (Translations.lambda0 c) (lambda0Coordinates c h))

/-- The module isomorphism used by the Postnikov argument. Its multiplicity
is the original Ext dimension, and its source is actual lattice restriction. -/
def lambda0_coordinate_layerIso (j : ℕ) (hj : 1 ≤ j) (hjD : j < D) :
    (lambda0Restriction c h).obj (Layers.layer c j) ≅
      coefficientVector (ZMod p) D (Layers.multiplicity c j) := by
  letI := h j hj hjD
  exact (coordinateCoefficientEquiv (Translations.lambda0 c) (lambda0Coordinates c h)
    (Layers.layer c j)
    (fun a m => (Translations.mem_lambda0_iff c a).mp a.property j hj hjD m)).toModuleIso ≪≫
      (ModuleCat.restrictScalars augmentation).mapIso
        (Module.finBasis (ZMod p) (Layers.coefficients (Layers.layer c j))).equivFun.toModuleIso

theorem lambda0_coordinate_finrank (j : ℕ) :
    Module.finrank (ZMod p)
      (Layers.coefficients ((lambda0Restriction c h).obj (Layers.layer c j))) =
        Layers.multiplicity c j :=
  coefficient_finrank (Translations.lambda0 c) (lambda0Coordinates c h) (Layers.layer c j)

end Lambda0
end
end Decoupling.HighDim.TrivialLayers
