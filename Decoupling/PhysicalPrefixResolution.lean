import Decoupling.MainTheorem

/-! # The supplied length-three physical free resolution (Appendix A) -/

namespace Decoupling.PhysicalPrefixResolution

open Matrix ResolutionExt

noncomputable section

variable {q s r : ℕ} (c : CSS.Checks q s r)

def exchange : CSS.Checks q r s := ⟨c.H_Z, c.H_X⟩

theorem exchange_topological (h : c.Topological) : (exchange c).Topological := ⟨h.2, h.1⟩

/-- The actual augmented sequence is
`0 → R^k → R^r → R^q → R^s → N → 0`, with the three supplied maps unchanged. -/
structure Resolution (k : ℕ) where
  Γ_Z : Matrix (Fin r) (Fin k) R
  zero₃ : dagger c.H_Z * Γ_Z = 0
  exact₂ : LinearMap.range Γ_Z.mulVecLin = LinearMap.ker (dagger c.H_Z).mulVecLin
  exact₁ : LinearMap.range (dagger c.H_Z).mulVecLin = LinearMap.ker c.H_X.mulVecLin
  injective₃ : Function.Injective Γ_Z.mulVecLin

theorem exists_resolution (hTop : c.Topological) : ∃ k : ℕ, Nonempty (Resolution c k) := by
  obtain ⟨k, ⟨h⟩⟩ := MainTheorem.exists_free_resolution (exchange c) (exchange_topological c hTop)
  refine ⟨k, ⟨{
    Γ_Z := h.Γ
    zero₃ := h.zero
    exact₂ := ?_
    exact₁ := hTop.1.symm
    injective₃ := h.injectiveΓ }⟩⟩
  ext v
  exact (h.exact₁ v).symm

def augmentation : (Fin s → R) →ₗ[R] c.N := (LinearMap.range c.H_X.mulVecLin).mkQ

theorem augmentation_surjective : Function.Surjective (augmentation c) :=
  (LinearMap.range c.H_X.mulVecLin).mkQ_surjective

theorem exact_augmentation : LinearMap.range c.H_X.mulVecLin = LinearMap.ker (augmentation c) :=
  (Submodule.ker_mkQ _).symm

end
end Decoupling.PhysicalPrefixResolution
