import Decoupling.HighDim.MinimalLatticeNative
import Decoupling.HighDim.TwoLayerNested

/-! # The mod-p image of a genuine inclusion Γ ⊆ Λ in normalized coordinates -/

namespace Decoupling.HighDim.MinimalLattice
noncomputable section

variable {p D : ℕ} [Fact p.Prime]

theorem reducedMap_range_eq_range_image (a : Translation D →+ Translation D) :
    LinearMap.range (KoszulLattice.reducedMap (ZMod p) a) = image p D a.range := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨b, rfl⟩ := reduction_surjective p D w
    rw [reduction_intertwines]
    exact ⟨a b, ⟨b, rfl⟩, rfl⟩
  · rintro ⟨w, ⟨b, rfl⟩, rfl⟩
    exact ⟨reduction p D b, reduction_intertwines a b⟩

variable (Λ Γ : AddSubgroup (Translation D)) (hΓ : Γ ≤ Λ)
  (eΛ : Λ ≃+ Translation D) (eΓ : Γ ≃+ Translation D)

theorem nested_range : (TwoLayer.nestedCoordinateMap Λ Γ hΓ eΛ eΓ).range =
    coordinateSubgroup Λ eΛ Γ := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact ⟨⟨(eΓ.symm b : Translation D), hΓ (eΓ.symm b).property⟩,
      (eΓ.symm b).property, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    refine ⟨eΓ ⟨b, hb⟩, ?_⟩
    change eΛ ((AddSubgroup.inclusion hΓ) (eΓ.symm (eΓ ⟨b, hb⟩))) = eΛ b
    rw [eΓ.symm_apply_apply]
    rfl

theorem nested_reducedMap_image :
    LinearMap.range (KoszulLattice.reducedMap (ZMod p)
      (TwoLayer.nestedCoordinateMap Λ Γ hΓ eΛ eΓ)) = image p D (coordinateSubgroup Λ eΛ Γ) := by
  rw [reducedMap_range_eq_range_image, nested_range]

end
end Decoupling.HighDim.MinimalLattice
