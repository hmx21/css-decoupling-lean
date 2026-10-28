import Decoupling.HighDim.GluedNativeFormality
import Decoupling.HighDim.TwoLayerCriterion
import Decoupling.HighDim.TorusSplitCount

/-!
# The actual example's two native layers and full translation kernel

All layer statements here are deduced from the proved comparison of the
literal check matrices with their genuine coupling cone.
-/
namespace Decoupling.HighDim.Glued
open CategoryTheory CategoryTheory.Limits PostnikovInduction TrivialLayers
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

def actualHomologyOneIso : H (Profile.S_X (checks K)) 1 ≅ Koszul.coefficientModule K 3 :=
  (DerivedCategory.homologyFunctor _ 1).mapIso (actualProfileConeIso K) ≪≫
    couplingCone_layerOneIso K

def actualHomologyTwoIso : H (Profile.S_X (checks K)) 2 ≅ Koszul.coefficientModule K 3 :=
  (DerivedCategory.homologyFunctor _ 2).mapIso (actualProfileConeIso K) ≪≫
    couplingCone_layerTwoIso K

def actualLayerOneIso : Layers.layer (checks K) 1 ≅ Koszul.coefficientModule K 3 :=
  (Profile.homologyEquivLayer (checks K) 0).toModuleIso.symm ≪≫ actualHomologyOneIso K

def actualLayerTwoIso : Layers.layer (checks K) 2 ≅ Koszul.coefficientModule K 3 :=
  (Profile.homologyEquivLayer (checks K) 1).toModuleIso.symm ≪≫ actualHomologyTwoIso K

def actualLayerIso (j : ℕ) (hj : j = 1 ∨ j = 2) :
    Layers.layer (checks K) j ≅ Koszul.coefficientModule K 3 :=
  if h : j = 1 then eqToIso (congrArg (Layers.layer (checks K)) h) ≪≫ actualLayerOneIso K
  else eqToIso (congrArg (Layers.layer (checks K)) (hj.resolve_left h)) ≪≫ actualLayerTwoIso K

def actualLayerCoefficientsIso (j : ℕ) (hj : j = 1 ∨ j = 2) :
    Layers.coefficients (Layers.layer (checks K) j) ≅ ModuleCat.of K K :=
  (ModuleCat.restrictScalars constant).mapIso (actualLayerIso K j hj) ≪≫
    Torus.coefficientModuleCoefficientsIso

theorem actualLayer_augmentation (j : ℕ) (hj : j = 1 ∨ j = 2) :
    AugmentationAction (Layers.layer (checks K) j) :=
  augmentationAction_of_iso (actualLayerIso K j hj) augmentationAction_coefficientModule

variable (p : ℕ) [Fact p.Prime]

theorem finiteXLayers : Layers.FiniteXLayers (checks (ZMod p)) := by
  intro j hj hjD
  exact Module.Finite.equiv (actualLayerCoefficientsIso (ZMod p) j (by omega)).symm.toLinearEquiv

theorem actualMultiplicity (j : ℕ) (hj : j = 1 ∨ j = 2) :
    Layers.multiplicity (checks (ZMod p)) j = 1 := by
  exact (actualLayerCoefficientsIso (ZMod p) j hj).toLinearEquiv.finrank_eq.trans
    (Module.finrank_self (ZMod p))

theorem actualSupport : Profile.support (checks (ZMod p)) = {1, 2} := by
  let : Nontrivial (Koszul.coefficientModule (ZMod p) 3) := inferInstanceAs (Nontrivial (ZMod p))
  ext i
  rw [Profile.mem_support_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨j, hj, hjD, _, rfl⟩
    omega
  · intro hi
    rcases hi with rfl | rfl
    · refine ⟨1, by omega, by omega, ?_, rfl⟩
      exact (actualLayerOneIso (ZMod p)).toLinearEquiv.surjective.nontrivial
    · refine ⟨2, by omega, by omega, ?_, rfl⟩
      exact (actualLayerTwoIso (ZMod p)).toLinearEquiv.surjective.nontrivial

theorem lambda0_eq_top : Translations.lambda0 (checks (ZMod p)) = ⊤ := by
  apply top_unique
  intro a _
  apply (Translations.mem_lambda0_iff _ a).mpr
  intro j hj hjD x
  have h := actualLayer_augmentation (ZMod p) j (by omega) (monomial (ZMod p) a) x
  simpa only [augmentation_monomial, map_one, one_smul] using h

end
end Decoupling.HighDim.Glued
