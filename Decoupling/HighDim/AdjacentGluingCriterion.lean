import Decoupling.HighDim.AdjacentGluing
import Decoupling.HighDim.DecouplingCriterionZ
import Decoupling.HighDim.TwoLayerCriterion

/-!
# HD010 translation-kernel and all-adjacent-gluing physical criterion

Finite layers are used only in this corollary, to identify the trivial
layers with the original finite toric multiplicities. There is no bound
on their number. Both actual scalar restriction and actual physical
coarse checks use the same prescribed subgroup.
-/
namespace Decoupling.HighDim.DecouplingCriterion
open CategoryTheory ScalingLattice
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable {p D q s r : ℕ} [Fact p.Prime]
  (Λ : AddSubgroup (Translation D)) [Λ.FiniteIndex] (e : Λ ≃+ Translation D)
  (c : CSS.Checks (ZMod p) D q s r)

/-- Necessity needs no finiteness assumption on the original layers. -/
theorem kernel_and_adjacent_of_decouples (hc : c.Topological) (hd : DecouplesOn Λ e c) :
    Λ ≤ Translations.lambda0 c ∧
      ∀ j : ℤ, AdjacentGluing.delta (TwoLayer.onLatticeProfile Λ e c) j = 0 := by
  obtain ⟨t, ht⟩ := hd
  refine ⟨TwoLayer.le_lambda0_of_decouples Λ e c (Toric.copyForms D t) (fun i => by
    have := i.1.isLt
    change i.1.val + 1 ≤ D
    omega) ht, ?_⟩
  obtain ⟨f⟩ := (decouples_to_multiplicities_iff Λ e c hc t).mp ht
  intro j
  rw [AdjacentGluing.delta_zero_iff_cutoff]
  exact AdjacentGluing.cutoff_cap_zero_of_cutoff_zero _ j
    (PostnikovTruncation.connecting_of_iso f j
      (Toric.splitTarget_connecting (ZMod p) D (Toric.copyForms D t) j))

/-- Arbitrary finite-layer criterion: trivial translations and every actual
adjacent attachment vanishing are jointly necessary and sufficient. -/
theorem decouples_iff_kernel_and_adjacent (hc : c.Topological) (hD : 1 ≤ D)
    (h : Layers.FiniteXLayers c) :
    DecouplesOn Λ e c ↔ Λ ≤ Translations.lambda0 c ∧
      ∀ j : ℤ, AdjacentGluing.delta (TwoLayer.onLatticeProfile Λ e c) j = 0 := by
  constructor
  · exact kernel_and_adjacent_of_decouples Λ e c hc
  · rintro ⟨hΛ, hδ⟩
    refine ⟨SplitMultiplicity.multiplicities c, ?_⟩
    apply TwoLayer.decouplesOn_of_formal Λ e c h hΛ hc
    exact (AdjacentGluing.formal_iff_all_delta (Profile.support c)
      (TwoLayer.onLatticeProfile Λ e c) (TwoLayer.onLattice_supported Λ e c hc hD)).mpr hδ

/-- The same all-layer criterion for the actual Z-side Fourier-dual word. -/
theorem decouples_Z_iff_kernel_and_adjacent (hc : c.Topological) (hD : 1 ≤ D)
    (h : Layers.FiniteZLayers c) :
    DecouplesOnZ Λ e c ↔ Λ ≤ Translations.lambda0 c.swap ∧
      ∀ j : ℤ, AdjacentGluing.delta (TwoLayer.onLatticeProfile Λ e c.swap) j = 0 := by
  rw [theorem1_Z Λ e c hc, ← theorem1_X Λ e c.swap (c.topological_swap hc)]
  exact decouples_iff_kernel_and_adjacent Λ e c.swap (c.topological_swap hc) hD h

end
end Decoupling.HighDim.DecouplingCriterion
