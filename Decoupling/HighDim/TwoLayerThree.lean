import Decoupling.HighDim.TwoLayerMinimum

/-!
# The three-dimensional physical minimum is exactly 1, p, or p²

Source: Corollary 2, HD008. Coefficients are genuine linear maps between
the two native homology layers; scalar-valued gluing is not assumed.
All three-dimensional codes satisfying the original assumptions are
covered, including zero and one nonzero layer.
-/

namespace Decoupling.HighDim.TwoLayer
open CategoryTheory CategoryTheory.Limits PostnikovInduction MinimalLattice
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {p q s r : ℕ} [Fact p.Prime]
  (c : CSS.Checks (ZMod p) 3 q s r) (h : Layers.FiniteXLayers c) (hc : c.Topological)

def threeCoefficients : Fin 3 → GluingValue c h 1 2 :=
  if hs : Profile.support c = {1, 2} then
    Three.coefficients (canonicalForm c h hc (by decide) 1 2 (by decide) hs)
  else 0

omit [Fact p.Prime] in
theorem support_subset_three : Profile.support c ⊆ {1, 2} := by
  intro i hi
  obtain ⟨n, hn, hnD, _, hni⟩ := (Profile.mem_support_iff c i).mp hi
  simp only [Finset.mem_insert, Finset.mem_singleton]
  omega

omit [Fact p.Prime] in
theorem atMostOne_of_not_two (hs : Profile.support c ≠ {1, 2}) :
    Layers.nonzeroLayerCount c ≤ 1 := by
  rw [← Profile.support_card]
  have hsub := support_subset_three c
  have hcard := Finset.card_le_card hsub
  have htwo : ({1, 2} : Finset ℤ).card = 2 := by decide
  rw [htwo] at hcard
  by_contra! hh
  exact hs (Finset.eq_of_subset_of_card_le hsub (by omega))

theorem threeDimensional_minimumIndex : IsLeast (DecouplingIndices c)
    (if ∀ i, threeCoefficients c h hc i = 0 then 1 else
      if LinearIndependent (ZMod p) (threeCoefficients c h hc) then p ^ 2 else p) := by
  by_cases hs : Profile.support c = {1, 2}
  · let := Translations.lambda0_finiteIndex c h
    let f := canonicalForm c h hc (by decide) 1 2 (by decide) hs
    have he : DecouplingIndices c = {n : ℕ | ∃ Γ : AddSubgroup (Translation 3),
        Γ ≤ Translations.lambda0 c ∧ Γ.FiniteIndex ∧
        Three.Isotropic (Three.coefficients f) (image p 3 (coordinateSubgroup
          (Translations.lambda0 c) (TrivialLayers.lambda0Coordinates c h) Γ)) ∧
        Γ.relIndex (Translations.lambda0 c) = n} := by
      ext n
      constructor
      · rintro ⟨Γ, hfin, hd, hn⟩
        let := hfin
        have hΓ := decouplesOn_le_lambda0 Γ (LatticeBasis.coordinates Γ) c hd
        have hv := (decouplesOn_iff_form_vanishes c h hc (by decide) 1 2 (by decide) hs
          Γ (LatticeBasis.coordinates Γ) hΓ).mp hd
        exact ⟨Γ, hΓ, hfin, (Three.alternating_vanishes_iff f _).mp hv, hn⟩
      · rintro ⟨Γ, hΓ, hfin, hv, hn⟩
        let := hfin
        exact ⟨Γ, hfin, (decouplesOn_iff_form_vanishes c h hc (by decide) 1 2 (by decide) hs
          Γ (LatticeBasis.coordinates Γ) hΓ).mpr ((Three.alternating_vanishes_iff f _).mpr hv), hn⟩
    rw [he]
    simpa only [threeCoefficients, dite_eq_left hs] using Three.relativeMinimumIndex_classification
      (p := p) (Three.coefficients f) (Translations.lambda0 c) (TrivialLayers.lambda0Coordinates c h)
  · simp only [threeCoefficients, dite_eq_right hs, Pi.zero_apply, implies_true, ↓reduceIte]
    exact decoupling_minimumIndex_of_atMostOne c h hc (by decide) (atMostOne_of_not_two c hs)

end
end Decoupling.HighDim.TwoLayer
