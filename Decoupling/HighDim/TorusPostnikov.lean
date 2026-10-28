import Decoupling.HighDim.TorusRepresentable
import Decoupling.HighDim.PostnikovInduction

/-!
# Summing the actual canonical Postnikov long exact sequences

Source: Appendix B.3. The represented dimension is bounded by the sum
of the represented dimensions of actual homology layers. Each exact
sequence is supplied by the canonical truncation triangle. Empty support
is included, and finiteness of the middle terms is proved inductively.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits
open PostnikovTruncation PostnikovInduction
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ}

def representedLayer (P X : Derived K D) (i : ℤ) : ModuleCat K :=
  homCoefficients P ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj (H X i))

/-- Native representable dimension obeys the complete finite Postnikov
bound. The finite-layer inputs concern actual homology, not a chosen
splitting or a replacement object. -/
theorem postnikov_finrank_le (P : Derived K D) :
    ∀ (s : Finset ℤ) (X : Derived K D), Supported X s →
      (∀ i ∈ s, Module.Finite K (representedLayer P X i)) →
      Module.Finite K (homCoefficients P X) ∧
      Module.finrank K (homCoefficients P X) ≤
        ∑ i ∈ s, Module.finrank K (representedLayer P X i) := by
  intro s
  refine Finset.strongInductionOn s (fun s ih => ?_)
  intro X hX hF
  by_cases hs : s.Nonempty
  · let j := s.max' hs
    have hj : j ∈ s := Finset.max'_mem s hs
    have hle : ∀ i ∈ s, i ≤ j := fun i hi => Finset.le_max' s i hi
    have hlt : ∀ i ∈ s.erase j, i < j := by
      intro i hi
      have hi' := Finset.mem_erase.mp hi
      have := hle i hi'.2
      omega
    have : X.IsLE j := supported_isLE hX j hle
    have he (i : ℤ) (hi : i ∈ s.erase j) :
        representedLayer P (lower X j) i ≅ representedLayer P X i :=
      homCoefficientsIso P ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).mapIso
        (lowerHomologyIso X j i (hlt i hi)))
    have hFL : ∀ i ∈ s.erase j, Module.Finite K (representedLayer P (lower X j) i) := by
      intro i hi
      let := hF i (Finset.mem_of_mem_erase hi)
      exact Module.Finite.equiv (he i hi).symm.toLinearEquiv
    obtain ⟨hLF, hLB⟩ := ih (s.erase j) (Finset.erase_ssubset hj) (lower X j)
      (lower_supported hX j) hFL
    let := hLF
    let := hF j hj
    let eU : homCoefficients P (upper X j) ≅ representedLayer P X j :=
      homCoefficientsIso P (upperSingleIso X j)
    let : Module.Finite K (homCoefficients P (upper X j)) :=
      Module.Finite.equiv eU.symm.toLinearEquiv
    let : Module.Finite K (homCoefficients P (triangle X j).obj₁) := hLF
    let : Module.Finite K (homCoefficients P (triangle X j).obj₃) := by
      change Module.Finite K (homCoefficients P (upper X j))
      infer_instance
    have hT := t.triangleLTGE_distinguished j X
    have hFinite := homCoefficients_finite_middle P (triangle X j) hT
    refine ⟨hFinite, ?_⟩
    have hb := triangle_finrank_le P (triangle X j) hT
    change Module.finrank K (homCoefficients P X) ≤
      Module.finrank K (homCoefficients P (lower X j)) +
        Module.finrank K (homCoefficients P (upper X j)) at hb
    rw [eU.toLinearEquiv.finrank_eq] at hb
    have hsums : (∑ i ∈ s.erase j, Module.finrank K (representedLayer P (lower X j) i)) =
        ∑ i ∈ s.erase j, Module.finrank K (representedLayer P X i) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (he i hi).toLinearEquiv.finrank_eq
    rw [hsums] at hLB
    calc
      Module.finrank K (homCoefficients P X) ≤
          (∑ i ∈ s.erase j, Module.finrank K (representedLayer P X i)) +
            Module.finrank K (representedLayer P X j) :=
        hb.trans (Nat.add_le_add_right hLB _)
      _ = ∑ i ∈ s, Module.finrank K (representedLayer P X i) :=
        Finset.sum_erase_add _ _ hj
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    have hLE : X.IsLE 0 := supported_isLE hX 0 (by simp)
    have hGE : X.IsGE 1 := supported_isGE hX 1 (by simp)
    have hzero : IsZero X := t.isZero X 0 1
    let : Subsingleton (homCoefficients P X) := ⟨fun f g => hzero.eq_of_tgt f g⟩
    constructor
    · infer_instance
    · simp only [Finset.sum_empty, Nat.le_zero]
      exact Module.finrank_eq_zero_of_subsingleton K _

end
end Decoupling.HighDim.Torus
