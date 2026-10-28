import Decoupling.HighDim.TorusPostnikov
import Decoupling.HighDim.ProfileSupport

/-!
# The binomial bound for the actual positive CSS profile

Source: Appendix B.3, the sum over the canonical truncation triangles.
This theorem uses only topology and finite native Ext layers. It concerns
the genuine represented profile dimension. Identifying that dimension with
the actual periodic logical quotient is a separate comparison, not assumed
or hidden in the definition of the logical-qudit number.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits
open PostnikovInduction
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {p D q s r : ℕ} [Fact p.Prime]

/-- The target number in the manuscript uses dimensions on the original
coefficient vector spaces and includes every positive degree below `D`. -/
def layerBound (c : CSS.Checks (ZMod p) D q s r) : ℕ :=
  ∑ j ∈ Finset.Ico 1 D, D.choose j * Layers.multiplicity c j

/-- The actual profile's represented layer identified with its native Ext
module, retaining the coefficient-field linear structure. -/
def profileRepresentedLayerIso (c : CSS.Checks (ZMod p) D q s r) (n : ℕ) :
    representedLayer (probe (ZMod p) D) (Profile.S_X c) (n + 1 : ℕ) ≅
      homCoefficients (probe (ZMod p) D)
        ((DerivedCategory.singleFunctor (ModuleCat (Laurent (ZMod p) D)) (n + 1 : ℕ)).obj
          (Layers.layer c (n + 1))) :=
  homCoefficientsIso _ ((DerivedCategory.singleFunctor _ (n + 1 : ℕ)).mapIso
    (Profile.homologyEquivLayer c n).toModuleIso)

/-- Genuine represented profile dimension is bounded by the binomial sum,
without augmentation-action or splitting assumptions on its layers. -/
theorem profile_finrank_le (c : CSS.Checks (ZMod p) D q s r)
    (hc : c.Topological) (hD : 1 ≤ D) (hF : Layers.FiniteXLayers c) :
    Module.Finite (ZMod p) (homCoefficients (probe (ZMod p) D) (Profile.S_X c)) ∧
    Module.finrank (ZMod p) (homCoefficients (probe (ZMod p) D) (Profile.S_X c)) ≤
      layerBound c := by
  have hSingle (i : ℤ) (hi : i ∈ Profile.support c) :
      Module.Finite (ZMod p) (representedLayer (probe (ZMod p) D) (Profile.S_X c) i) := by
    obtain ⟨n, hn, hnD, _, rfl⟩ := (Profile.mem_support_iff c i).mp hi
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    let := hF (n + 1) (by omega) hnD
    let := probeSingle_finite (Layers.layer c (n + 1)) (n + 1)
      (D - (n + 1) - 1) (by omega)
    exact Module.Finite.equiv (profileRepresentedLayerIso c n).symm.toLinearEquiv
  obtain ⟨hFinite, hBound⟩ := postnikov_finrank_le (probe (ZMod p) D) (Profile.support c)
    (Profile.S_X c) (Profile.homology_isZero_outside_support c hc hD) hSingle
  refine ⟨hFinite, hBound.trans ?_⟩
  have hTerm (n : ℕ) (hn : n ∈ Profile.supportNat c) :
      Module.finrank (ZMod p) (representedLayer (probe (ZMod p) D) (Profile.S_X c) n) ≤
        D.choose n * Layers.multiplicity c n := by
    have hn' := Finset.mem_filter.mp hn
    have hnD := Finset.mem_range.mp hn'.1
    obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
    let := hF (n + 1) hn'.2.1 hnD
    rw [(profileRepresentedLayerIso c n).toLinearEquiv.finrank_eq]
    exact probeSingle_finrank_le (Layers.layer c (n + 1)) (n + 1) hnD
  have hsum : (∑ i ∈ Profile.support c,
      Module.finrank (ZMod p) (representedLayer (probe (ZMod p) D) (Profile.S_X c) i)) =
        ∑ n ∈ Profile.supportNat c,
          Module.finrank (ZMod p) (representedLayer (probe (ZMod p) D) (Profile.S_X c) n) := by
    rw [Profile.support, Finset.sum_image]
    intro a _ b _ hab
    exact Nat.cast_injective hab
  rw [hsum]
  calc
    _ ≤ ∑ n ∈ Profile.supportNat c, D.choose n * Layers.multiplicity c n :=
      Finset.sum_le_sum hTerm
    _ ≤ layerBound c := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        have hn' := Finset.mem_filter.mp hn
        exact Finset.mem_Ico.mpr ⟨hn'.2.1, Finset.mem_range.mp hn'.1⟩
      · intro n _ _
        exact Nat.zero_le _

end
end Decoupling.HighDim.Torus
