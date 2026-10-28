import Decoupling.HighDim.KoszulFiniteRestrictionExt
import Decoupling.HighDim.TrivialLayers

/-!
# Lemma 1: actual positive Ext restriction is zero

Source: `drafts/main.tex`, Lemma `lem:ext-zero`. The only module hypotheses are finite
coefficient dimension of the source and augmentation annihilation of both
modules. In particular, no resolution, comparison map, regular sequence,
Ext presentation, or vanishing assertion is an input. Those are constructed
in the imported Koszul modules, with arbitrary dimension and characteristic.
The conclusion concerns the actual native restriction map, not the target
Ext group. The target module need not have finite coefficient dimension.
-/

namespace Decoupling.HighDim.ExtRestrictionVanishing

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Preadditive
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ}

/-- Annihilation by the actual augmentation ideal gives the actual
augmentation scalar action. -/
theorem augmentationAction_of_ideal_annihilates (M : ModuleCat (Laurent K D))
    (h : ∀ a ∈ augmentationIdeal K D, ∀ m : M, a • m = 0) :
    TrivialLayers.AugmentationAction M := by
  intro a m
  have ha : a - constant (augmentation a) ∈ augmentationIdeal K D := by
    rw [← ker_augmentation_eq]
    simp [RingHom.mem_ker]
  have hh := h _ ha m
  simpa only [sub_smul, sub_eq_zero] using hh

theorem difference_annihilates_of_augmentationAction (M : ModuleCat (Laurent K D))
    (h : TrivialLayers.AugmentationAction M) (i : Fin D) (m : M) :
    difference K i • m = 0 := by
  rw [h]
  simp

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- Lemma 1 in the standard Laurent category, with the actual augmentation
action as its module hypothesis. -/
theorem of_augmentationAction (A B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients A)]
    (hA : TrivialLayers.AugmentationAction A) (hB : TrivialLayers.AugmentationAction B)
    (n : ℕ) (e : Ext A B (n + 1)) :
    e.mapExactFunctor (ModuleCat.restrictScalars (Koszul.scaling K D p)) = 0 := by
  let t := Module.finrank K (Layers.coefficients A)
  let i : A ≅ TrivialLayers.coefficientVector K D t := TrivialLayers.coordinateIso A hA
  apply Koszul.finite_source_ext_restriction_eq_zero K D p (ι := Fin t) A B
    (fun j => TrivialLayers.coordinateInclusion K D t j ≫ i.inv)
    (fun j => i.hom ≫ TrivialLayers.coordinateProjection K D t j) _
    (difference_annihilates_of_augmentationAction B hB) n e
  calc
    ∑ j, (i.hom ≫ TrivialLayers.coordinateProjection K D t j) ≫
        (TrivialLayers.coordinateInclusion K D t j ≫ i.inv) =
      i.hom ≫ (∑ j, TrivialLayers.coordinateProjection K D t j ≫
        TrivialLayers.coordinateInclusion K D t j) ≫ i.inv := by
          simp only [comp_sum, sum_comp, Category.assoc]
    _ = 𝟙 A := by rw [TrivialLayers.sum_projection_inclusion]; simp

/-- Every strictly positive native Ext class between the stated modules
restricts to zero under one actual p-scaling step. -/
theorem of_ideal_annihilates (A B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients A)]
    (hA : ∀ a ∈ augmentationIdeal K D, ∀ m : A, a • m = 0)
    (hB : ∀ a ∈ augmentationIdeal K D, ∀ m : B, a • m = 0)
    (j : ℕ) (hj : 0 < j) (e : Ext A B j) :
    e.mapExactFunctor (ModuleCat.restrictScalars (Koszul.scaling K D p)) = 0 := by
  cases j with
  | zero => omega
  | succ n =>
    exact of_augmentationAction p A B
      (augmentationAction_of_ideal_annihilates A hA)
      (augmentationAction_of_ideal_annihilates B hB) n e

/-- Equality of the actual entire additive restriction map to zero. -/
theorem mapExtAddHom_eq_zero (A B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients A)]
    (hA : ∀ a ∈ augmentationIdeal K D, ∀ m : A, a • m = 0)
    (hB : ∀ a ∈ augmentationIdeal K D, ∀ m : B, a • m = 0)
    (j : ℕ) (hj : 0 < j) :
    (ModuleCat.restrictScalars (Koszul.scaling K D p)).mapExtAddHom A B j = 0 := by
  ext e
  exact of_ideal_annihilates p A B hA hB j hj e

end
end Decoupling.HighDim.ExtRestrictionVanishing
