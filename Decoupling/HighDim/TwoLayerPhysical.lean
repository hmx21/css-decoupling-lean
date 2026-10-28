import Decoupling.HighDim.ToricSplitCircuit
import Decoupling.HighDim.ProfileStabilityCircuit
import Decoupling.HighDim.ToricStackNativeProfile

/-!
# Native-profile necessity for physical decoupling

Source: necessity in Corollaries 2 and 3, HD008. A physical word of
SUM/SWAP gates transporting both stabilized check images gives an
isomorphism of the original native profiles. Ancilla and identity-check
invariance are applied to the actual matrices in `DecouplesToStack`.
This statement has no two-layer assumption and is also used for Corollary 3.
-/

namespace Decoupling.HighDim.Toric
open CategoryTheory ProfileStability
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ} {ι : Type} [Fintype ι] (forms : ι → ℕ)
  {q s r : ℕ} (c : CSS.Checks K D q s r)

/-- Physical decoupling implies equality of native derived profiles,
without assuming either source or target is already split. -/
theorem profileIso_of_decouples (h : DecouplesToStack K D forms c) :
    Nonempty (Profile.S_X c ≅ Profile.S_X (stackChecks K D forms)) := by
  classical
  obtain ⟨a, b, gates, ht, _⟩ := h
  exact ⟨(identityChecksProfileIso (I := Fin a) c.H_X).symm ≪≫
    (ancillaProfileIso
      (A := Fin (stackCount D forms 0) ⊕ Fin b)
      (B := Fin (stackCount D forms 1) ⊕ (Fin s ⊕ Fin a))
      (StableCSS.identityChecks (A := Fin a) c.H_X)).symm ≪≫
    circuitProfileIso gates (Equiv.sumComm _ _) _ _ _ _ ht ≪≫
    ancillaProfileIso
      (A := Fin s ⊕ Fin a)
      (B := Fin q ⊕ (Fin (stackCount D forms 0) ⊕ Fin b))
      (StableCSS.identityChecks (A := Fin b) (stackChecks K D forms).H_X) ≪≫
    identityChecksProfileIso (I := Fin b) (stackChecks K D forms).H_X⟩

/-- Same-lattice physical decoupling is exactly native split-profile formality.
The target range includes the manuscript's positive toric types. -/
theorem decouples_iff_split (hc : c.Topological) (hforms : ∀ i, forms i + 1 ≤ D) :
    DecouplesToStack K D forms c ↔ Nonempty (Profile.S_X c ≅ splitTarget K D forms) := by
  constructor
  · intro h
    obtain ⟨e⟩ := profileIso_of_decouples forms c h
    exact ⟨e ≪≫ stackChecks_nativeProfileIso K D forms hforms⟩
  · rintro ⟨e⟩
    exact decouples_of_split K D forms c hc e

end
end Decoupling.HighDim.Toric
