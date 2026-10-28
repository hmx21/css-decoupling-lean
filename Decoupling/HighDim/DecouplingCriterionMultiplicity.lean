import Decoupling.HighDim.AdjacentGluingCriterion

/-! # Existential toric targets and the original native multiplicities -/
namespace Decoupling.HighDim.DecouplingCriterion
open CategoryTheory
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable {p D q s r : ℕ} [Fact p.Prime]
  (Λ : AddSubgroup (Translation D)) [Λ.FiniteIndex] (e : Λ ≃+ Translation D)
  (c : CSS.Checks (ZMod p) D q s r)

/-- With finite native layers, existence of any toric target is equivalent
to physical decoupling onto the target with the original multiplicities.
The necessity follows from actual adjacent gluing, not a finrank convention. -/
theorem decouples_iff_original_multiplicities (hc : c.Topological) (hD : 1 ≤ D)
    (h : Layers.FiniteXLayers c) : DecouplesOn Λ e c ↔ TwoLayer.DecouplesOn Λ e c := by
  constructor
  · intro hd
    obtain ⟨hΛ, hδ⟩ := kernel_and_adjacent_of_decouples Λ e c hc hd
    apply TwoLayer.decouplesOn_of_formal Λ e c h hΛ hc
    exact (AdjacentGluing.formal_iff_all_delta (Profile.support c)
      (TwoLayer.onLatticeProfile Λ e c) (TwoLayer.onLattice_supported Λ e c hc hD)).mpr hδ
  · intro hd
    exact ⟨SplitMultiplicity.multiplicities c, hd⟩

end
end Decoupling.HighDim.DecouplingCriterion
