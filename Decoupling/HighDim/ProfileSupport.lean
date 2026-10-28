import Decoupling.HighDim.ProfileBounds

/-! # The exact finite support of the native positive CSS profile -/

namespace Decoupling.HighDim.Profile

open CategoryTheory CategoryTheory.Limits
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable

variable {p D q s r : ℕ} [Fact p.Prime]

def supportNat (c : CSS.Checks (ZMod p) D q s r) : Finset ℕ :=
  (Finset.range D).filter (fun j => 1 ≤ j ∧ Nontrivial (Layers.E_X c j))

def support (c : CSS.Checks (ZMod p) D q s r) : Finset ℤ :=
  (supportNat c).image (fun n : ℕ => (n : ℤ))

omit [Fact p.Prime] in
theorem mem_support_iff (c : CSS.Checks (ZMod p) D q s r) (i : ℤ) :
    i ∈ support c ↔ ∃ n : ℕ, 1 ≤ n ∧ n < D ∧ Nontrivial (Layers.E_X c n) ∧ (n : ℤ) = i := by
  simp only [support, supportNat, Finset.mem_image, Finset.mem_filter, Finset.mem_range]
  aesop

omit [Fact p.Prime] in
theorem support_card (c : CSS.Checks (ZMod p) D q s r) :
    (support c).card = Layers.nonzeroLayerCount c := by
  exact Finset.card_image_of_injective _ Nat.cast_injective

theorem homology_isZero_outside_support (c : CSS.Checks (ZMod p) D q s r)
    (hc : c.Topological) (hD : 1 ≤ D) (i : ℤ) (hi : i ∉ support c) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat (Laurent (ZMod p) D)) i).obj (S_X c)) := by
  by_cases hi0 : i < 1
  · exact DerivedCategory.isZero_of_isGE (S_X c) 1 i hi0
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : 0 ≤ i)
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    have hsub : Subsingleton (Layers.E_X c (n + 1)) := by
      by_cases hn : n + 1 < D
      · apply not_nontrivial_iff_subsingleton.mp
        intro hN
        exact hi ((mem_support_iff c _).mpr ⟨n + 1, by omega, hn, hN, rfl⟩)
      · exact DegreeBound.ext_subsingleton c hc hD (by omega)
    exact ModuleCat.isZero_iff_subsingleton.mpr (homologyEquivLayer c n).injective.subsingleton

end
end Decoupling.HighDim.Profile
