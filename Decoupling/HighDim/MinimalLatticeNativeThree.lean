import Decoupling.HighDim.MinimalLatticeNative

/-! # Three-dimensional actual restriction minimum, with Hom-valued coefficients -/

namespace Decoupling.HighDim.MinimalLattice.Three
open CategoryTheory CategoryTheory.Abelian
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable

variable {p : ℕ} [Fact p.Prime]
  (B A : ModuleCat (Laurent (ZMod p) 3))
  [FiniteDimensional (ZMod p) (Layers.coefficients B)]
  (hB : TrivialLayers.AugmentationAction B) (hA : TrivialLayers.AugmentationAction A)
  (κ : Ext B A 2)

theorem nativeRestriction_minimumIndex_classification :
    IsLeast {n : ℕ | ∃ (Γ : AddSubgroup (Translation 3)) (hfin : Γ.FiniteIndex),
      κ.mapExactFunctor (nativeRestriction (p := p) Γ (@LatticeBasis.coordinates 3 Γ hfin)) = 0 ∧
        Γ.index = n}
      (if ∀ i, nativeCoefficients B A hB hA κ i = 0 then 1 else
        if LinearIndependent (ZMod p) (nativeCoefficients B A hB hA κ) then p ^ 2 else p) := by
  have he : {n : ℕ | ∃ (Γ : AddSubgroup (Translation 3)) (hfin : Γ.FiniteIndex),
      κ.mapExactFunctor (nativeRestriction (p := p) Γ (@LatticeBasis.coordinates 3 Γ hfin)) = 0 ∧
        Γ.index = n} =
      {n : ℕ | ∃ Γ : AddSubgroup (Translation 3), Γ.FiniteIndex ∧
        (∀ v : Fin 2 → Residue p 3, (∀ i, v i ∈ image p 3 Γ) →
          ExtValues.nativeAlternatingEquiv B A hB hA 2 κ v = 0) ∧ Γ.index = n} := by
    ext n
    constructor <;> rintro ⟨Γ, hfin, hk, hn⟩ <;> let := hfin
    · exact ⟨Γ, hfin, (native_restriction_eq_zero_iff Γ (LatticeBasis.coordinates Γ)
        B A hB hA 2 κ).mp hk, hn⟩
    · exact ⟨Γ, hfin, (native_restriction_eq_zero_iff Γ (LatticeBasis.coordinates Γ)
        B A hB hA 2 κ).mpr hk, hn⟩
  rw [he]
  exact nativeMinimumIndex_classification B A hB hA κ

end
end Decoupling.HighDim.MinimalLattice.Three
