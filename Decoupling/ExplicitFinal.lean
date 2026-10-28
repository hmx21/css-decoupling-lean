import Decoupling.ExplicitAlgorithm
import Decoupling.FinalDecoupling

/-!
# The final decoupling theorem with the selected algorithm matrices

This strengthens `FinalDecoupling` by constructing the printed T, C, V, V′
and choosing exactly `φ₀=(T V′)` in the resulting physical/circuit certificate.
All retained periods, layer identifications and obstruction vanishing are
derived from the original data. This modular interface takes a native
free-resolution (or freeness proof); `ExplicitMain.decoupling` supplies it from
the internally proved Swan theorem and needs only the manuscript assumptions.
-/

namespace Decoupling.ExplicitFinal

open Matrix EvaluationLinear LayerTranslations ResolutionExt FinalDecoupling

noncomputable section

set_option synthInstance.maxSize 512
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {q s r cX : ℕ} (c : CSS.Checks q s r) (h : CSSResolution c cX)

def finalResolution (n : ℕ+) : CSSResolution (finalChecks n c) (finalCoverRank n cX) :=
  CoarseCSS.resolution 2 (CoarseCSS.resolution (n : ℕ) h)

/-- The complete output retains the actual representative data and its exact
relationship to the chosen comparison and physical circuit. -/
structure Result (n : ℕ+) extends FinalDecoupling.Result c cX n where
  layer₁ : Trivial (layerRank c 1) ≃ₗ[R] (finalResolution c h n).cochain.C1
  layer₂ : (finalResolution c h n).cochain.C2 ≃ₗ[R] Trivial (layerRank c 2)
  data : ExplicitAlgorithm.Data (finalResolution c h n).cochain layer₁ layer₂
  selected_φ₀ : certificate.comparison.φ₀ = data.φ₀
  selected_β : certificate.β = data.β

/-- The whole original-to-coarse-to-circuit construction, now preserving the
literal Appendix C matrices. No desired algorithm data is an input. -/
theorem exists_result (hTop : c.Topological)
    [FiniteDimensional (ZMod 2) (coefficients (layer c 1))]
    [FiniteDimensional (ZMod 2) (coefficients (layer c 2))] :
    ∃ n : ℕ+, Nonempty (Result c h n) := by
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
  obtain ⟨a, cert, hφ, hβ⟩ := ExplicitAlgorithm.exists_explicit_certificate
    (CoarseCSS.resolution 2 h₁) d₁.symm d₂
    (CoarseCSS.topological 2 c₁ hTop₁) hκ
  exact ⟨npos, ⟨{
    dimension₁ := (CoarseExt.E1_finrank 2 h₁).trans (CoarseExt.E1_finrank n h)
    dimension₂ := (CoarseExt.E2_finrank 2 h₁).trans (CoarseExt.E2_finrank n h)
    certificate := cert
    layer₁ := d₁.symm
    layer₂ := d₂
    data := a
    selected_φ₀ := hφ
    selected_β := hβ
  }⟩⟩

/-- A selected full output with the actual printed matrices retained. -/
def construct (hTop : c.Topological)
    [FiniteDimensional (ZMod 2) (coefficients (layer c 1))]
    [FiniteDimensional (ZMod 2) (coefficients (layer c 2))] :
    Σ n : ℕ+, Result c h n :=
  ⟨Classical.choose (exists_result c h hTop),
    Classical.choice (Classical.choose_spec (exists_result c h hTop))⟩

/-- Alternate modular input: native finite-projective Laurent freeness.
`ExplicitMain` supplies the internally proved instance of this theorem. -/
theorem exists_result_of_laurent_freeness (hTop : c.Topological)
    [FiniteDimensional (ZMod 2) (coefficients (layer c 1))]
    [FiniteDimensional (ZMod 2) (coefficients (layer c 2))]
    (hfreeness : ∀ M : ModuleCat.{0} R, Module.Finite R M → Module.Projective R M →
      Module.Free R M) :
    ∃ cX : ℕ, ∃ h : CSSResolution c cX, ∃ n : ℕ+, Nonempty (Result c h n) := by
  obtain ⟨cX, ⟨h⟩⟩ := FreeResolution.exists_free_resolution_of_global_bound_and_freeness
    c hTop LaurentGlobalDimension.laurent_global_bound hfreeness
  obtain ⟨n, hn⟩ := exists_result c h hTop
  exact ⟨cX, h, n, hn⟩

namespace Result

variable {c h} {n : ℕ+} (out : Result c h n)

/-- The final circuit's selected degree-zero comparison is the literal block
`(T, V+T C V(1))` of the manuscript, in its original species ordering. -/
theorem literal_φ₀ : out.certificate.comparison.φ₀ =
    Matrix.fromCols out.data.T
      (out.data.V + out.data.T * (out.data.C * out.data.V.map augmentation).map constant) :=
  out.selected_φ₀

/-- The final selected representative matrix consists of actual cycles. -/
theorem γ_T : (finalResolution c h n).cochain.γ.comp out.data.T.mulVecLin = 0 :=
  out.data.γ_T

/-- The final selected basis expansion is a boundary exactly on augmentation-zero
coefficients, for every Laurent vector. -/
theorem T_boundary_iff (v : Fin (layerRank c 1) → R) :
    out.data.T *ᵥ v ∈ LinearMap.range (finalResolution c h n).cochain.d₁ ↔
      augmentation ∘ v = 0 := out.data.T_boundary_iff v

end Result

end
end Decoupling.ExplicitFinal
