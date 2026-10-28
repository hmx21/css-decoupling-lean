import Decoupling.HighDim.TorusProfileBound

/-!
# Maximal represented profile dimension forces trivial layer actions

Source: Appendix B.3. The result uses the full canonical Postnikov bound:
a strictly smaller contribution at any actual layer makes the total bound
strict, regardless of all gluing classes. Trivial actions are a consequence
of equality, never an assumption about the input CSS code.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits PostnikovInduction
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {p D q s r : ℕ} [Fact p.Prime]

/-- A nontrivial layer action creates strict loss in the complete native
profile bound, even when the profile has arbitrarily many nonsplit layers. -/
theorem profile_finrank_lt_of_nontrivial_action (c : CSS.Checks (ZMod p) D q s r)
    (hc : c.Topological) (hD : 1 ≤ D) (hF : Layers.FiniteXLayers c)
    (j : ℕ) (hj : 1 ≤ j) (hjD : j < D)
    (ha : ¬ TrivialLayers.AugmentationAction (Layers.layer c j)) :
    Module.finrank (ZMod p) (homCoefficients (probe (ZMod p) D) (Profile.S_X c)) <
      layerBound c := by
  have hjN : Nontrivial (Layers.E_X c j) := by
    by_contra hn
    let : Subsingleton (Layers.E_X c j) := not_nontrivial_iff_subsingleton.mp hn
    let : Subsingleton (Layers.layer c j) := by
      change Subsingleton (Layers.E_X c j)
      infer_instance
    apply ha
    intro a m
    exact Subsingleton.elim _ _
  have hjs : (j : ℤ) ∈ Profile.support c :=
    (Profile.mem_support_iff c j).mpr ⟨j, hj, hjD, hjN, rfl⟩
  have hFinite (i : ℤ) (hi : i ∈ Profile.support c) :
      Module.Finite (ZMod p) (representedLayer (probe (ZMod p) D) (Profile.S_X c) i) := by
    obtain ⟨n, hn, hnD, _, rfl⟩ := (Profile.mem_support_iff c i).mp hi
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    let := hF (n + 1) (by omega) hnD
    let := probeSingle_finite (Layers.layer c (n + 1)) (n + 1)
      (D - (n + 1) - 1) (by omega)
    exact Module.Finite.equiv (profileRepresentedLayerIso c n).symm.toLinearEquiv
  have hp := (postnikov_finrank_le (probe (ZMod p) D) (Profile.support c)
    (Profile.S_X c) (Profile.homology_isZero_outside_support c hc hD) hFinite).2
  let weight : ℤ → ℕ := fun i => D.choose i.toNat * Layers.multiplicity c i.toNat
  have hTerm (i : ℤ) (hi : i ∈ Profile.support c) :
      Module.finrank (ZMod p) (representedLayer (probe (ZMod p) D) (Profile.S_X c) i) ≤
        weight i := by
    obtain ⟨n, hn, hnD, _, rfl⟩ := (Profile.mem_support_iff c i).mp hi
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    let := hF (n + 1) (by omega) hnD
    rw [(profileRepresentedLayerIso c n).toLinearEquiv.finrank_eq]
    exact probeSingle_finrank_le (Layers.layer c (n + 1)) (n + 1) hnD
  have hStrict :
      Module.finrank (ZMod p) (representedLayer (probe (ZMod p) D) (Profile.S_X c) j) <
        weight j := by
    apply lt_of_le_of_ne (hTerm j hjs)
    intro heq
    apply ha
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    let := hF (n + 1) hj hjD
    rw [(profileRepresentedLayerIso c n).toLinearEquiv.finrank_eq] at heq
    exact (probeSingle_finrank_eq_iff (Layers.layer c (n + 1)) (n + 1) hj hjD).mp heq
  have hsumlt := Finset.sum_lt_sum hTerm ⟨(j : ℤ), hjs, hStrict⟩
  apply (lt_of_le_of_lt hp hsumlt).trans_le
  change (∑ i ∈ Profile.support c, weight i) ≤ _
  rw [Profile.support, Finset.sum_image]
  · change (∑ n ∈ Profile.supportNat c, D.choose n * Layers.multiplicity c n) ≤ _
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      have hn' := Finset.mem_filter.mp hn
      exact Finset.mem_Ico.mpr ⟨hn'.2.1, Finset.mem_range.mp hn'.1⟩
    · intro n _ _
      exact Nat.zero_le _
  · intro a _ b _ hab
    exact Nat.cast_injective hab

/-- Equality forces trivial translation action on every original native
Ext layer; no layer was assumed trivial in the proof. -/
theorem profile_equality_implies_augmentation (c : CSS.Checks (ZMod p) D q s r)
    (hc : c.Topological) (hD : 1 ≤ D) (hF : Layers.FiniteXLayers c)
    (heq : Module.finrank (ZMod p)
      (homCoefficients (probe (ZMod p) D) (Profile.S_X c)) = layerBound c)
    (j : ℕ) (hj : 1 ≤ j) (hjD : j < D) :
    TrivialLayers.AugmentationAction (Layers.layer c j) := by
  by_contra ha
  have hlt := profile_finrank_lt_of_nontrivial_action c hc hD hF j hj hjD ha
  omega

end
end Decoupling.HighDim.Torus
