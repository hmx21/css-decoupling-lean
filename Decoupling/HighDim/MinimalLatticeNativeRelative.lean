import Decoupling.HighDim.MinimalLatticeNested

/-!
# Relative optimal index for a family of actual native Ext restrictions

Source: Proposition 1, HD008. Λ can be any finite-index retained lattice,
with no rectangular assumption. Native Ext classes are over its group
algebra in arbitrary integer coordinates; every restriction is along the
actual inclusion of Γ into Λ in the independently selected bases.
-/

namespace Decoupling.HighDim.MinimalLattice
open CategoryTheory CategoryTheory.Abelian
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable

variable {p D : ℕ} [Fact p.Prime]
  (Λ : AddSubgroup (Translation D)) (eΛ : Λ ≃+ Translation D)
  {ι : Type*} (degree : ι → ℕ) (B A : ι → ModuleCat (Laurent (ZMod p) D))
  [∀ i, FiniteDimensional (ZMod p) (Layers.coefficients (B i))]
  (hB : ∀ i, TrivialLayers.AugmentationAction (B i))
  (hA : ∀ i, TrivialLayers.AugmentationAction (A i)) (κ : ∀ i, Ext (B i) (A i) (degree i))

def RelativeKills (Γ : AddSubgroup (Translation D)) (hΓ : Γ ≤ Λ) (eΓ : Γ ≃+ Translation D) : Prop :=
  ∀ i, (κ i).mapExactFunctor (ModuleCat.restrictScalars (KoszulLattice.latticeMap (ZMod p)
    (TwoLayer.nestedCoordinateMap Λ Γ hΓ eΛ eΓ))) = 0

theorem relativeKills_iff (Γ : AddSubgroup (Translation D)) (hΓ : Γ ≤ Λ)
    (eΓ : Γ ≃+ Translation D) :
    RelativeKills Λ eΛ degree B A κ Γ hΓ eΓ ↔
      VanishesOn degree (fun i => Layers.coefficients (B i) →ₗ[ZMod p] Layers.coefficients (A i))
        (nativeForms degree B A hB hA κ) (image p D (coordinateSubgroup Λ eΛ Γ)) := by
  simp only [RelativeKills, VanishesOn, nativeForms,
    KoszulLattice.finite_restriction_eq_zero_iff_image _ _ _ (hB _) (hA _),
    nested_reducedMap_image]

theorem native_relativeMinimumIndex_isLeast [Λ.FiniteIndex] (positive : ∀ i, 0 < degree i) :
    IsLeast {n : ℕ | ∃ (Γ : AddSubgroup (Translation D)) (hfin : Γ.FiniteIndex) (hΓ : Γ ≤ Λ),
      RelativeKills Λ eΛ degree B A κ Γ hΓ (@LatticeBasis.coordinates D Γ hfin) ∧ Γ.relIndex Λ = n}
      (p ^ minimumCodim degree
        (fun i => Layers.coefficients (B i) →ₗ[ZMod p] Layers.coefficients (A i))
        (nativeForms degree B A hB hA κ) positive) := by
  have he : {n : ℕ | ∃ (Γ : AddSubgroup (Translation D)) (hfin : Γ.FiniteIndex) (hΓ : Γ ≤ Λ),
      RelativeKills Λ eΛ degree B A κ Γ hΓ (@LatticeBasis.coordinates D Γ hfin) ∧ Γ.relIndex Λ = n} =
      {n : ℕ | ∃ Γ : AddSubgroup (Translation D), Γ ≤ Λ ∧ Γ.FiniteIndex ∧
        VanishesOn degree _ (nativeForms degree B A hB hA κ)
          (image p D (coordinateSubgroup Λ eΛ Γ)) ∧ Γ.relIndex Λ = n} := by
    ext n
    constructor
    · rintro ⟨Γ, hfin, hΓ, hk, hn⟩
      let := hfin
      exact ⟨Γ, hΓ, hfin, (relativeKills_iff Λ eΛ degree B A hB hA κ Γ hΓ _).mp hk, hn⟩
    · rintro ⟨Γ, hΓ, hfin, hk, hn⟩
      let := hfin
      exact ⟨Γ, hfin, hΓ, (relativeKills_iff Λ eΛ degree B A hB hA κ Γ hΓ _).mpr hk, hn⟩
  rw [he]
  exact relativeMinimum_isLeast Λ eΛ _ _ _ positive

end
end Decoupling.HighDim.MinimalLattice
