import Decoupling.HighDim.ToricStackNativeProfile
import Decoupling.HighDim.TrivialLayers

/-!
# Trivial translation action is necessary for a toric split profile

Every cohomology module of the genuine derived toric-stack target has
augmentation action. The proof uses cohomology of the single complexes
and the actual finite biproduct. No action condition on the original code
is assumed.
-/

namespace Decoupling.HighDim.TrivialLayers

open CategoryTheory CategoryTheory.Limits
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [CommRing K] {D : ℕ}

theorem augmentationAction_of_iso {M N : ModuleCat (Laurent K D)}
    (e : M ≅ N) (h : AugmentationAction N) : AugmentationAction M := by
  intro a m
  apply e.toLinearEquiv.injective
  simpa only [map_smul] using h a (e.toLinearEquiv m)

theorem augmentationAction_coefficientModule : AugmentationAction (Koszul.coefficientModule K D) := by
  intro a m
  change augmentation a * (show K from m) =
    augmentation (constant (augmentation a)) * (show K from m)
  rw [augmentation_constant]

theorem augmentationAction_biproduct {ι : Type} [Fintype ι]
    (M : ι → ModuleCat (Laurent K D)) (h : ∀ i, AugmentationAction (M i)) :
    AugmentationAction (⨁ M) := by
  apply augmentationAction_of_iso (ModuleCat.biproductIsoPi M)
  intro a m
  funext i
  exact h i a (m i)

theorem augmentationAction_singleHomology (j n : ℤ) :
    AugmentationAction ((DerivedCategory.homologyFunctor (ModuleCat (Laurent K D)) n).obj
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj
        (Koszul.coefficientModule K D))) := by
  by_cases hn : n = j
  · subst n
    exact augmentationAction_of_iso
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat (Laurent K D)) j).app
        (Koszul.coefficientModule K D)) augmentationAction_coefficientModule
  · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat (Laurent K D)) n).obj
        ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj
          (Koszul.coefficientModule K D))) := by
      rcases lt_or_gt_of_ne hn with hlt | hgt
      · exact DerivedCategory.isZero_of_isGE _ j n hlt
      · exact DerivedCategory.isZero_of_isLE _ j n hgt
    intro a m
    exact (ModuleCat.subsingleton_of_isZero hz).elim _ _

end
end Decoupling.HighDim.TrivialLayers

namespace Decoupling.HighDim.Toric

open CategoryTheory CategoryTheory.Limits
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (D : ℕ) {ι : Type} [Fintype ι] (forms : ι → ℕ)

theorem splitTarget_homology_augmentationAction (n : ℤ) :
    TrivialLayers.AugmentationAction
      ((DerivedCategory.homologyFunctor (ModuleCat (Laurent K D)) n).obj
        (splitTarget K D forms)) := by
  apply TrivialLayers.augmentationAction_of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat (Laurent K D)) n).mapBiproduct
      (fun i => (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) (forms i + 1)).obj
        (Koszul.coefficientModule K D)))
  exact TrivialLayers.augmentationAction_biproduct _
    (fun i => TrivialLayers.augmentationAction_singleHomology (forms i + 1) n)

theorem augmentationAction_of_nativeSplit {q s r : ℕ} (c : CSS.Checks K D q s r)
    (e : Profile.S_X c ≅ splitTarget K D forms) (n : ℕ) :
    TrivialLayers.AugmentationAction (Layers.layer c (n + 1)) := by
  apply TrivialLayers.augmentationAction_of_iso
    ((Profile.homologyEquivLayer c n).symm.toModuleIso ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat (Laurent K D)) (n + 1 : ℕ)).mapIso e)
  exact splitTarget_homology_augmentationAction K D forms (n + 1 : ℕ)

end
end Decoupling.HighDim.Toric
