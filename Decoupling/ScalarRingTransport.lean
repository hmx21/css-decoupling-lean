import Decoupling.CoarseVanishing
import Decoupling.CoarseExt

/-!
# Renaming the literal doubled subring

The explicit doubling proof uses `S ⊆ R`. Expanded CSS checks instead use
the renamed Laurent ring, with scalar action through the power-two embedding.
The two embeddings agree. A literal S-linear splitting therefore becomes an
R-linear splitting of the renamed restricted cochain; the genuine Ext splice
then vanishes there as well.
-/

namespace Decoupling.ScalarRingTransport

open CategoryTheory CategoryTheory.Abelian RetainedRing EvaluationLinear

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

/-- General retained-lattice doubling is the same literal coefficient embedding. -/
theorem embed_two : GeneralRetained.embed 2 = RetainedRing.embed := rfl

variable {q s k : ℕ}
variable (c : Syndrome.Cochain R (Fin q → R) (Fin s → R) (Fin k → R))

/-- Rename the scalars of an actual S-linear section without changing its function. -/
def renameSection
    (σ : (ScalarRestriction.restricted S c).L →ₗ[S]
      (ScalarRestriction.restricted S c).N) :
    (CoarseExt.restrictCochain 2 c).L →ₗ[R] (CoarseExt.restrictCochain 2 c).N where
  toFun := σ
  map_add' := σ.map_add
  map_smul' r a := by
    change σ ((renameEquiv r) • (show (ScalarRestriction.restricted S c).L from a)) =
      (renameEquiv r) • σ (show (ScalarRestriction.restricted S c).L from a)
    exact σ.map_smul (renameEquiv r) a

theorem renameSection_identity
    (σ : (ScalarRestriction.restricted S c).L →ₗ[S]
      (ScalarRestriction.restricted S c).N)
    (hσ : (ScalarRestriction.restricted S c).π.comp σ = LinearMap.id) :
    (CoarseExt.restrictCochain 2 c).π.comp (renameSection c σ) = LinearMap.id := by
  apply LinearMap.ext
  intro a
  exact DFunLike.congr_fun hσ a

/-- Renaming preserves vanishing of this genuine splice, via the actual
section, without postulating any cross-ring Ext equality. -/
theorem κ_renamed_eq_zero_of_section
    (σ : (ScalarRestriction.restricted S c).L →ₗ[S]
      (ScalarRestriction.restricted S c).N)
    (hσ : (ScalarRestriction.restricted S c).π.comp σ = LinearMap.id) :
    (CoarseExt.restrictCochain 2 c).κ = 0 := by
  have hfirst : (CoarseExt.restrictCochain 2 c).first_shortExact.extClass = 0 :=
    (ExtSplitting.extClass_zero_iff_section _).mpr
      ⟨ModuleCat.ofHom (renameSection c σ), ModuleCat.hom_ext (renameSection_identity c σ hσ)⟩
  change (CoarseExt.restrictCochain 2 c).second_shortExact.extClass.comp
    (CoarseExt.restrictCochain 2 c).first_shortExact.extClass _ = 0
  rw [hfirst, Ext.comp_zero]

/-- Concrete II.1 after the retained variables have been renamed. -/
theorem κ_renamed_eq_zero {t : ℕ} (e₂ : c.C2 ≃ₗ[R] Trivial t)
    (hu : ∀ e : c.C1, u • e = 0) (hv : ∀ e : c.C1, v • e = 0)
    (hw : ∀ e : c.C1, w • e = 0) : (CoarseExt.restrictCochain 2 c).κ = 0 := by
  obtain ⟨σ, hσ⟩ := CoarseVanishing.exists_restricted_section c e₂ hu hv hw
  exact κ_renamed_eq_zero_of_section c σ hσ

end
end Decoupling.ScalarRingTransport
