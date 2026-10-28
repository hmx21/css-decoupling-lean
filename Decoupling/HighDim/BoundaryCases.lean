import Decoupling.HighDim.DegreeBound
import Decoupling.HighDim.LatticeBasis
import Mathlib.Order.Interval.Finset.Nat

/-!
# Empty and sparse superselection layers

The layer count is taken from genuine positive Ext groups. These results
justify the zero-layer branch of the lattice construction and the bound
m ≤ D-1, without silently assuming a first nonzero layer exists.
The zero-profile and product-state decoupling conclusions still require
the later derived-profile and circuit theorems.
-/

namespace Decoupling.HighDim.BoundaryCases
noncomputable section
attribute [local instance] Classical.propDecidable

variable {p D q s r : ℕ}

theorem nonzeroLayerCount_le_pred (c : CSS.Checks (ZMod p) D q s r) :
    Layers.nonzeroLayerCount c ≤ D - 1 := by
  calc
    Layers.nonzeroLayerCount c ≤ (Finset.Ico 1 D).card := by
      apply Finset.card_le_card
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_range] at hj
      exact Finset.mem_Ico.mpr ⟨hj.2.1, hj.1⟩
    _ = D - 1 := Nat.card_Ico 1 D

theorem nonzeroLayerCount_eq_zero_iff (c : CSS.Checks (ZMod p) D q s r) :
    Layers.nonzeroLayerCount c = 0 ↔
      ∀ j : ℕ, 1 ≤ j → j < D → Subsingleton (Layers.E_X c j) := by
  rw [Layers.nonzeroLayerCount, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  constructor
  · intro h j hj hjD
    apply not_nontrivial_iff_subsingleton.mp
    intro hn
    exact h (Finset.mem_range.mpr hjD) ⟨hj, hn⟩
  · intro h j hj hn
    have hs := h j hn.1 (Finset.mem_range.mp hj)
    exact (not_nontrivial_iff_subsingleton.mpr hs) hn.2

variable [Fact p.Prime]

theorem lambda0_eq_top_of_no_layers (c : CSS.Checks (ZMod p) D q s r)
    (hm : Layers.nonzeroLayerCount c = 0) : Translations.lambda0 c = ⊤ := by
  apply top_unique
  intro a _
  apply (Translations.mem_lambda0_iff c a).mpr
  intro j hj hjD e
  have hs := (nonzeroLayerCount_eq_zero_iff c).mp hm j hj hjD
  exact hs.elim _ _

theorem finalLattice_eq_top_of_no_layers (c : CSS.Checks (ZMod p) D q s r)
    (hm : Layers.nonzeroLayerCount c = 0) :
    LatticeBasis.finalLattice (Translations.lambda0 c) p (Layers.nonzeroLayerCount c) = ⊤ := by
  rw [hm, LatticeBasis.finalLattice_zero, lambda0_eq_top_of_no_layers c hm]

end
end Decoupling.HighDim.BoundaryCases
