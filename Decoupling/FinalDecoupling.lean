import Decoupling.ScalarRingTransport
import Decoupling.DecouplingFromSplitting
import Decoupling.FreeResolution
import Decoupling.LaurentGlobalDimension

/-!
# The complete decoupling construction after a supplied native free resolution

Starting from the original CSS checks, both topological equalities, finite
genuine positive Ext layers, and an actual finite-free resolution, this file
constructs a common positive retained period, then doubles it, expands the
actual CSS matrices, proves the obstruction vanishes, and constructs the
stable standard-target equivalence and finite CNOT circuit.

The species multiplicities are the original `𝔽₂` dimensions of the genuine
`Ext_Rⁱ(overline M_X,R)` layers. Neither layer identifications, κ vanishing,
augmentation isomorphisms, comparison data, nor circuits are input assumptions.
The final target uses the manuscript's direction-first Koszul ordering, with
the free `h` summand in degree zero only.

This modular interface takes a native `CSSResolution`, or alternatively a
native Laurent-projective freeness theorem. `SwanInduction` proves that theorem
and `MainTheorem.decoupling` discharges both inputs. `ExplicitMain` additionally
retains the literal algorithm matrices in the final output.
-/

namespace Decoupling.FinalDecoupling

open Matrix EvaluationLinear LayerTranslations ResolutionExt

noncomputable section

set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {q s r : ℕ}

/-- Multiplicities are the dimensions of the genuine original Ext layers. -/
def layerRank (c : CSS.Checks q s r) (i : ℕ) : ℕ :=
  Module.finrank (ZMod 2) (coefficients (layer c i))

/-- The literal two-stage expanded CSS presentation: retain n, then double. -/
def finalChecks (n : ℕ+) (c : CSS.Checks q s r) :
    CSS.Checks (CoarseCSS.size 2 (CoarseCSS.size (n : ℕ) q))
      (CoarseCSS.size 2 (CoarseCSS.size (n : ℕ) s))
      (CoarseCSS.size 2 (CoarseCSS.size (n : ℕ) r)) :=
  CoarseCSS.checks 2 (CoarseCSS.checks (n : ℕ) c)

def finalCoverRank (n : ℕ+) (cX : ℕ) : ℕ :=
  CoarseCSS.size 2 (CoarseCSS.size (n : ℕ) cX)

theorem final_size (n : ℕ+) (k : ℕ) :
    CoarseCSS.size 2 (CoarseCSS.size (n : ℕ) k) = k * (2 * (n : ℕ)) ^ 3 := by
  simp only [CoarseCSS.size_eq, mul_pow]
  ring

/-- The actual complete output includes genuine Ext dimension preservation
and the full stable matrix/circuit certificate of Sections III–IV. -/
structure Result (c : CSS.Checks q s r) (cX : ℕ) (n : ℕ+) where
  dimension₁ : layerRank (finalChecks n c) 1 = layerRank c 1
  dimension₂ : layerRank (finalChecks n c) 2 = layerRank c 2
  certificate : DecouplingFromSplitting.Certificate (finalChecks n c)
    (finalCoverRank n cX) (layerRank c 1) (layerRank c 2)

/-- Evaluation is unchanged by taking any integer power of each translation. -/
theorem augmentation_embed (n : ℕ) (r : R) :
    augmentation (GeneralRetained.embed n r) = augmentation r := by
  have he : (augmentation.comp (GeneralRetained.embed n)).toAddMonoidHom =
      augmentation.toAddMonoidHom := by
    apply AddMonoidAlgebra.addMonoidHom_ext
    intro a t
    simp [GeneralRetained.embed]
  exact DFunLike.congr_fun he r

/-- A trivial translation module remains the same trivial module on every
retained lattice, with no change in its number of copies. -/
def restrictTrivial (n t : ℕ) :
    CoarseExt.Restrict n (Trivial t) ≃ₗ[R] Trivial t where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    funext j
    change augmentation (GeneralRetained.embed n r) * x j = augmentation r * x j
    rw [augmentation_embed]

theorem annihilates_of_equiv {M : Type*} [AddCommGroup M] [Module R M] {t : ℕ}
    (e : M ≃ₗ[R] Trivial t) (a : R) (ha : augmentation a = 0) (m : M) :
    a • m = 0 := by
  apply e.injective
  rw [map_smul, map_zero]
  funext j
  change augmentation a * e m j = 0
  rw [ha, zero_mul]

variable (c : CSS.Checks q s r) {cX : ℕ} (h : CSSResolution c cX)

include h in
/-- Full construction with the actual finite-free resolution as its sole
remaining upstream algebraic input. The retained period and every subsequent
isomorphism, comparison, and circuit are constructed in this theorem. -/
theorem exists_result (hTop : c.Topological)
    [FiniteDimensional (ZMod 2) (coefficients (layer c 1))]
    [FiniteDimensional (ZMod 2) (coefficients (layer c 2))] :
    ∃ n : ℕ+, Nonempty (Result c cX n) := by
  obtain ⟨n, hn, ⟨e₁⟩, ⟨e₂⟩⟩ := RetainedLayers.exists_trivial_retained_layers c
  let npos : ℕ+ := ⟨n, hn⟩
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  let c₁ := CoarseCSS.checks n c
  let h₁ := CoarseCSS.resolution n h
  let b₁ : h₁.cochain.C1 ≃ₗ[R] Trivial (layerRank c 1) :=
    h₁.C1EquivE_X.trans ((CoarseExt.E1Equiv n h).trans e₁)
  let b₂ : h₁.cochain.C2 ≃ₗ[R] Trivial (layerRank c 2) :=
    h₁.C2EquivE_X.trans ((CoarseExt.E2Equiv n h).trans e₂)
  have hu : ∀ e : h₁.cochain.C1, u • e = 0 :=
    annihilates_of_equiv b₁ u augmentation_u
  have hv : ∀ e : h₁.cochain.C1, v • e = 0 :=
    annihilates_of_equiv b₁ v augmentation_v
  have hw : ∀ e : h₁.cochain.C1, w • e = 0 :=
    annihilates_of_equiv b₁ w augmentation_w
  have hκ : (CoarseCSS.resolution 2 h₁).cochain.κ = 0 :=
    (CoarseExt.κ_zero_iff_restricted 2 h₁).mpr
      (ScalarRingTransport.κ_renamed_eq_zero h₁.cochain b₂ hu hv hw)
  let d₁ : (CoarseCSS.resolution 2 h₁).cochain.C1 ≃ₗ[R] Trivial (layerRank c 1) :=
    (CoarseExt.cochainEquiv 2 h₁).C1Equiv.symm |>.trans
      (CoarseExt.restrictC1Equiv 2 h₁.cochain) |>.trans
      (CoarseExt.restrictEquiv 2 b₁) |>.trans (restrictTrivial 2 (layerRank c 1))
  let d₂ : (CoarseCSS.resolution 2 h₁).cochain.C2 ≃ₗ[R] Trivial (layerRank c 2) :=
    (CoarseExt.cochainEquiv 2 h₁).C2Equiv.symm |>.trans
      (CoarseExt.restrictC2Equiv 2 h₁.cochain) |>.trans
      (CoarseExt.restrictEquiv 2 b₂) |>.trans (restrictTrivial 2 (layerRank c 2))
  have hTop₁ : c₁.Topological := CoarseCSS.topological n c hTop
  obtain ⟨cert⟩ := DecouplingFromSplitting.exists_certificate
    (CoarseCSS.topological 2 c₁ hTop₁) (CoarseCSS.resolution 2 h₁) d₁.symm d₂ hκ
  refine ⟨npos, ⟨{ dimension₁ := ?_, dimension₂ := ?_, certificate := cert }⟩⟩
  · exact (CoarseExt.E1_finrank 2 h₁).trans (CoarseExt.E1_finrank n h)
  · exact (CoarseExt.E2_finrank 2 h₁).trans (CoarseExt.E2_finrank n h)

/-- A selected positive period with its fully constructed decoupling result. -/
def construct (hTop : c.Topological)
    [FiniteDimensional (ZMod 2) (coefficients (layer c 1))]
    [FiniteDimensional (ZMod 2) (coefficients (layer c 2))] :
    Σ n : ℕ+, Result c cX n :=
  ⟨Classical.choose (exists_result c h hTop),
    Classical.choice (Classical.choose_spec (exists_result c h hTop))⟩

/-- Replacing the supplied resolution by the one genuinely unresolved native
Laurent-projective freeness theorem. The uniform global dimension bound used
here is the proved theorem, not a further input. -/
theorem exists_result_of_laurent_freeness (hTop : c.Topological)
    [FiniteDimensional (ZMod 2) (coefficients (layer c 1))]
    [FiniteDimensional (ZMod 2) (coefficients (layer c 2))]
    (hfreeness : ∀ M : ModuleCat.{0} R, Module.Finite R M → Module.Projective R M →
      Module.Free R M) :
    ∃ cX : ℕ, ∃ n : ℕ+, Nonempty (Result c cX n) := by
  obtain ⟨cX, ⟨h⟩⟩ := FreeResolution.exists_free_resolution_of_global_bound_and_freeness
    c hTop LaurentGlobalDimension.laurent_global_bound hfreeness
  obtain ⟨n, hn⟩ := exists_result c h hTop
  exact ⟨cX, n, hn⟩

end
end Decoupling.FinalDecoupling
