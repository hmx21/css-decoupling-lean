import Decoupling.HighDim.MinimalLatticeRestriction
import Decoupling.HighDim.MinimalLatticeThreeNative
import Decoupling.HighDim.KoszulLatticeFiniteExt

/-!
# Proposition 1 for actual scalar restriction of native Ext classes

Source: Proposition 1 and the Ext² minimum in Corollary 2, HD008.
The predicates below use mathlib's genuine Ext and the exact restriction
functor along the actual subgroup inclusion. The minimum is attained by
the inverse image of an actual minimizing mod-p subspace.
-/

namespace Decoupling.HighDim.MinimalLattice
open CategoryTheory CategoryTheory.Abelian
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable

variable {p D : ℕ} [Fact p.Prime]

/-- Scalar restriction along the subgroup inclusion in any integer basis. -/
abbrev nativeRestriction (Γ : AddSubgroup (Translation D)) (e : Γ ≃+ Translation D) :=
  ModuleCat.restrictScalars (ScalingLattice.coordinateEmbedding (ZMod p) Γ e)

theorem native_restriction_eq_zero_iff (Γ : AddSubgroup (Translation D))
    (e : Γ ≃+ Translation D) (B A : ModuleCat (Laurent (ZMod p) D))
    [FiniteDimensional (ZMod p) (Layers.coefficients B)]
    (hB : TrivialLayers.AugmentationAction B) (hA : TrivialLayers.AugmentationAction A)
    (n : ℕ) (κ : Ext B A n) :
    κ.mapExactFunctor (nativeRestriction (p := p) Γ e) = 0 ↔
      ∀ v : Fin n → Residue p D, (∀ i, v i ∈ image p D Γ) →
        ExtValues.nativeAlternatingEquiv B A hB hA n κ v = 0 := by
  unfold nativeRestriction
  rw [← latticeMap_eq_coordinateEmbedding Γ e (ZMod p)]
  exact (KoszulLattice.finite_restriction_eq_zero_iff_alternating
    (inclusionCoordinates Γ e) B A hB hA n κ).trans (comp_reducedMap_zero_iff Γ e _)

variable {ι : Type*} (degree : ι → ℕ)
  (B A : ι → ModuleCat (Laurent (ZMod p) D))
  [∀ i, FiniteDimensional (ZMod p) (Layers.coefficients (B i))]
  (hB : ∀ i, TrivialLayers.AugmentationAction (B i))
  (hA : ∀ i, TrivialLayers.AugmentationAction (A i)) (κ : ∀ i, Ext (B i) (A i) (degree i))

abbrev nativeForms := fun i => ExtValues.nativeAlternatingEquiv (B i) (A i) (hB i) (hA i)
  (degree i) (κ i)

def Kills (Γ : AddSubgroup (Translation D)) [Γ.FiniteIndex] : Prop :=
  ∀ i, (κ i).mapExactFunctor (nativeRestriction (p := p) Γ (LatticeBasis.coordinates Γ)) = 0

theorem kills_iff (Γ : AddSubgroup (Translation D)) [Γ.FiniteIndex] :
    Kills degree B A κ Γ ↔ VanishesOn degree
      (fun i => Layers.coefficients (B i) →ₗ[ZMod p] Layers.coefficients (A i))
        (nativeForms degree B A hB hA κ) (image p D Γ) := by
  simp only [Kills, VanishesOn, nativeForms,
    native_restriction_eq_zero_iff Γ (LatticeBasis.coordinates Γ) _ _ (hB _) (hA _)]

/-- Exact minimum for simultaneous genuine restriction, with differing
positive degrees and differing source and target modules. -/
theorem native_minimumIndex_isLeast (positive : ∀ i, 0 < degree i) :
    IsLeast {n : ℕ | ∃ (Γ : AddSubgroup (Translation D)) (hfin : Γ.FiniteIndex),
      @Kills p D _ ι degree B A κ Γ hfin ∧ Γ.index = n}
      (p ^ minimumCodim degree
        (fun i => Layers.coefficients (B i) →ₗ[ZMod p] Layers.coefficients (A i))
        (nativeForms degree B A hB hA κ) positive) := by
  have he : {n : ℕ | ∃ (Γ : AddSubgroup (Translation D)) (hfin : Γ.FiniteIndex),
      @Kills p D _ ι degree B A κ Γ hfin ∧ Γ.index = n} =
      {n : ℕ | ∃ Γ : AddSubgroup (Translation D), Γ.FiniteIndex ∧
        VanishesOn degree _ (nativeForms degree B A hB hA κ) (image p D Γ) ∧ Γ.index = n} := by
    ext n
    constructor <;> rintro ⟨Γ, hfin, hΓ, hn⟩ <;> let := hfin
    · exact ⟨Γ, hfin, (kills_iff degree B A hB hA κ Γ).mp hΓ, hn⟩
    · exact ⟨Γ, hfin, (kills_iff degree B A hB hA κ Γ).mpr hΓ, hn⟩
  rw [he]
  exact minimumIndex_isLeast _ _ _ positive

include hB hA in
theorem native_primeToIndex_injective (Γ : AddSubgroup (Translation D)) [Γ.FiniteIndex]
    (hindex : ¬p ∣ Γ.index) : Kills degree B A κ Γ ↔ ∀ i, κ i = 0 := by
  rw [kills_iff degree B A hB hA κ Γ,
    vanishesOn_image_iff_zero_of_not_dvd_index degree _ _ Γ hindex]
  constructor
  · intro hh i
    exact (ExtValues.nativeAlternatingEquiv (B i) (A i) (hB i) (hA i) (degree i)).injective
      ((hh i).trans (map_zero _).symm)
  · intro hh i
    simp only [nativeForms, hh i, map_zero]

end
end Decoupling.HighDim.MinimalLattice
