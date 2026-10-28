import Decoupling.HighDim.Profile
import Decoupling.HighDim.BoundaryCases

/-!
# Cohomological support and the genuinely zero profile

Lemma 3 places the actual derived profile in degrees `[1,D-1]`.
If the number of nonzero positive Ext layers is zero, the derived object
itself is zero. This does not yet identify a physical trivializing circuit.
-/

namespace Decoupling.HighDim.Profile

open CategoryTheory CategoryTheory.Limits
noncomputable section
attribute [local instance] HasDerivedCategory.standard

variable {K : Type} [Field K] {D q s r : ℕ}

theorem S_X_isLE (c : CSS.Checks K D q s r) (hc : c.Topological) (hD : 1 ≤ D) :
    (S_X c).IsLE ((D : ℤ) - 1) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  have hi0 : 0 < i := by omega
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi0.le
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hs := DegreeBound.ext_subsingleton c hc hD (j := n + 1) (by omega)
  apply ModuleCat.isZero_iff_subsingleton.mpr
  exact (homologyEquivLayer c n).injective.subsingleton

variable {p : ℕ} [Fact p.Prime]

theorem S_X_isZero_of_no_layers (c : CSS.Checks (ZMod p) D q s r)
    (hc : c.Topological) (hD : 1 ≤ D) (hm : Layers.nonzeroLayerCount c = 0) :
    IsZero (S_X c) := by
  have hLE : (S_X c).IsLE 0 := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hi.le
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hs : Subsingleton (Layers.E_X c (n + 1)) := by
      by_cases hn : n + 1 < D
      · exact (BoundaryCases.nonzeroLayerCount_eq_zero_iff c).mp hm _ (by omega) hn
      · exact DegreeBound.ext_subsingleton c hc hD (by omega)
    apply ModuleCat.isZero_iff_subsingleton.mpr
    exact (homologyEquivLayer c n).injective.subsingleton
  exact DerivedCategory.TStructure.t.isZero (S_X c) 0 1

end
end Decoupling.HighDim.Profile
