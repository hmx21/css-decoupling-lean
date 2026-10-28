import Decoupling.HighDim.TorusPostnikovRigidity
import Decoupling.HighDim.TorusYonedaDetection
import Decoupling.HighDim.TorusSplitCount

/-!
# Maximal native torus-probe dimension forces formality

All inputs of the categorical rigidity induction are discharged by the
proved Laurent Koszul Yoneda detection theorem. Finite dimensionality and
augmentation action concern the actual homology objects.
-/

namespace Decoupling.HighDim.Torus
open CategoryTheory CategoryTheory.Limits PostnikovInduction
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ}

/-- The exact homology property needed after maximality has forced all
translation actions to become trivial. -/
def FiniteAugmentation (A : ModuleCat (Laurent K D)) : Prop :=
  Module.Finite K (Layers.coefficients A) ∧ TrivialLayers.AugmentationAction A

theorem finiteAugmentation_of_iso {A B : ModuleCat (Laurent K D)} (e : A ≅ B)
    (h : FiniteAugmentation A) : FiniteAugmentation B := by
  let : Module.Finite K (Layers.coefficients A) := h.1
  refine ⟨?_, TrivialLayers.augmentationAction_of_iso e.symm h.2⟩
  let ec : Layers.coefficients A ≅ Layers.coefficients B :=
    (ModuleCat.restrictScalars (constant : K →+* Laurent K D)).mapIso e
  exact Module.Finite.equiv ec.toLinearEquiv

theorem probeSingle_finite_int (A : ModuleCat (Laurent K D)) (i : ℤ)
    [Module.Finite K (Layers.coefficients A)] (hi : 1 ≤ i) (hiD : i < D) :
    Module.Finite K (homCoefficients (probe K D)
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj A)) := by
  obtain ⟨j, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
  exact probeSingle_finite A j (D - j - 1) (by omega)

/-- No detection or faithfulness assumption remains: it is supplied by
the proved native Koszul Yoneda theorem. -/
theorem probe_formal_of_maximal (s : Finset ℤ) (X : Derived K D)
    (hX : Supported X s) (hdeg : ∀ i ∈ s, 1 ≤ i ∧ i < D)
    (hQ : ∀ i ∈ s, FiniteAugmentation (H X i))
    (heq : Module.finrank K (homCoefficients (probe K D) X) =
      ∑ i ∈ s, Module.finrank K (representedLayer (probe K D) X i)) :
    Nonempty (X ≅ TwoLayer.homologySum X s) := by
  apply postnikov_formal_of_maximal (probe K D) FiniteAugmentation
    (fun e h => finiteAugmentation_of_iso e h) ?_ ?_ s X hX hdeg hQ heq
  · intro A i hA hi hiD
    let := hA.1
    exact probeSingle_finite_int A i hi hiD
  · intro A B i j hA hB hi hij hj f hf
    let := hA.1
    exact probe_detects_connecting A B hA.2 hB.2 i j hi hij hj f hf

theorem finrank_hom_homologySum (P X : Derived K D) (s : Finset ℤ)
    (hF : ∀ i ∈ s, Module.Finite K (representedLayer P X i)) :
    Module.finrank K (homCoefficients P (TwoLayer.homologySum X s)) =
      ∑ i ∈ s, Module.finrank K (representedLayer P X i) := by
  let : ∀ i : s, Module.Finite K (homCoefficients P
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj (H X i))) :=
    fun i => hF i i.property
  rw [TwoLayer.homologySum, FiniteBiproduct.sumObj, finrank_hom_biproduct]
  exact Finset.sum_attach s (fun i => Module.finrank K (representedLayer P X i))

def coefficientVectorCoefficientsIso (t : ℕ) :
    Layers.coefficients (TrivialLayers.coefficientVector K D t) ≅
      ModuleCat.of K (Fin t → K) :=
  (augmentationCoefficientsIso K D).app (ModuleCat.of K (Fin t → K))

theorem finiteAugmentation_coefficientVector (t : ℕ) :
    FiniteAugmentation (TrivialLayers.coefficientVector K D t) := by
  refine ⟨Module.Finite.equiv
    (coefficientVectorCoefficientsIso (K := K) (D := D) t).symm.toLinearEquiv, ?_⟩
  intro a m
  change augmentation a • (show (Fin t → K) from m) =
    augmentation (constant (augmentation a)) • (show (Fin t → K) from m)
  rw [augmentation_constant]

end
end Decoupling.HighDim.Torus
