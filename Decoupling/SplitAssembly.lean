import Decoupling.ExplicitSplitting
import Decoupling.ResolutionExt

/-! From vanishing of the genuine obstruction to the normalized augmentation. -/

namespace Decoupling.SplitAssembly

open CategoryTheory CategoryTheory.Abelian EvaluationLinear

noncomputable section

variable {q s k t₁ t₂ : ℕ}
variable (c : Syndrome.Cochain R (Fin q → R) (Fin s → R) (Fin k → R))

/-- The genuine splitting theorem supplies the retraction used in Appendix C. -/
theorem exists_retraction_of_κ_zero (hκ : c.κ = 0)
    (e₁ : Trivial t₁ ≃ₗ[R] c.C1) :
    ∃ p : c.N →ₗ[R] Trivial t₁,
      p.comp (c.ι.comp e₁.toLinearMap) = LinearMap.id := by
  obtain ⟨σ⟩ := c.κ_zero_iff_splitting.mp hκ
  refine ⟨e₁.symm.toLinearMap.comp σ.r.hom, ?_⟩
  have hr : σ.r.hom.comp c.ι = LinearMap.id := ModuleCat.hom_ext_iff.mp σ.f_r
  ext v
  change e₁.symm (σ.r.hom (c.ι (e₁ v))) = v
  have hv : σ.r.hom (c.ι (e₁ v)) = e₁ v := DFunLike.congr_fun hr (e₁ v)
  exact (congrArg e₁.symm hv).trans (e₁.symm_apply_apply v)

/-- Construct β from κ=0 and the two actual trivial-layer identifications.
There is no retraction, section, normalized cover, or β among the inputs. -/
def augmentationIsoOfκZero (hκ : c.κ = 0)
    (e₁ : Trivial t₁ ≃ₗ[R] c.C1) (e₂ : c.C2 ≃ₗ[R] Trivial t₂) :
    (Trivial t₁ × ((Fin (k - t₂) → R) × (Fin t₂ → J))) ≃ₗ[R] c.N :=
  let p := Classical.choose (exists_retraction_of_κ_zero c hκ e₁)
  ExplicitSplitting.augmentationIso c e₁ e₂ p
    (Classical.choose_spec (exists_retraction_of_κ_zero c hκ e₁))

/-- One empty endpoint automatically kills the obstruction, as in III.4. -/
theorem κ_zero_of_first_layer_zero [Subsingleton c.C1] : c.κ = 0 := by
  have hid : 𝟙 (ModuleCat.of R c.C1) = 0 := by
    apply ModuleCat.hom_ext
    ext v
    exact Subsingleton.elim _ _
  have h := Ext.comp_mk₀_id c.κ
  rw [hid, Ext.mk₀_zero, Ext.comp_zero] at h
  exact h.symm

theorem κ_zero_of_second_layer_zero [Subsingleton c.C2] : c.κ = 0 := by
  have hid : 𝟙 (ModuleCat.of R c.C2) = 0 := by
    apply ModuleCat.hom_ext
    ext v
    exact Subsingleton.elim _ _
  have h := Ext.mk₀_id_comp c.κ
  rw [hid, Ext.mk₀_zero, Ext.zero_comp] at h
  exact h.symm

end
end Decoupling.SplitAssembly
