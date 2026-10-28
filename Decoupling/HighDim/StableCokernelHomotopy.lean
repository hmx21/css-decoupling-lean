import Decoupling.HighDim.StableCokernel

/-!
# From homotopy identities to errors on actual cokernels

This is the degree-one calculation of `drafts/appendix.tex`, lines 511–555.
The modules below are actual quotients by the ranges of the degree-zero
differentials. A commuting pair of maps induces a map on these quotients.
The equation `id - φψ = d h₀ + h₁ d` then gives a factorization of its error
through the degree-two module. Thus the error factorizations needed by
`StableCokernel` are proved from linear homotopy identities rather than
assumed at the quotient level. Constructing the homotopy inverse from a
derived profile isomorphism remains a separate upstream theorem.
-/

namespace Decoupling.HighDim.StableCokernel

universe u v

variable {R : Type u} [Ring R]
variable {C₀ C₁ C₂ T₀ T₁ : Type v}
  [AddCommGroup C₀] [AddCommGroup C₁] [AddCommGroup C₂]
  [AddCommGroup T₀] [AddCommGroup T₁]
  [Module R C₀] [Module R C₁] [Module R C₂]
  [Module R T₀] [Module R T₁]

/-- A commuting square induces a map on the actual check cokernels. -/
def cokernelMap (dC : C₀ →ₗ[R] C₁) (dT : T₀ →ₗ[R] T₁)
    (f₀ : C₀ →ₗ[R] T₀) (f₁ : C₁ →ₗ[R] T₁)
    (hf : f₁.comp dC = dT.comp f₀) :
    (C₁ ⧸ LinearMap.range dC) →ₗ[R] (T₁ ⧸ LinearMap.range dT) :=
  (LinearMap.range dC).mapQ (LinearMap.range dT) f₁ (by
    rintro _ ⟨c, rfl⟩
    exact ⟨f₀ c, (DFunLike.congr_fun hf c).symm⟩)

@[simp] theorem cokernelMap_mk (dC : C₀ →ₗ[R] C₁) (dT : T₀ →ₗ[R] T₁)
    (f₀ : C₀ →ₗ[R] T₀) (f₁ : C₁ →ₗ[R] T₁)
    (hf : f₁.comp dC = dT.comp f₀) (c : C₁) :
    cokernelMap dC dT f₀ f₁ hf ((LinearMap.range dC).mkQ c) =
      (LinearMap.range dT).mkQ (f₁ c) := rfl

/-- The next differential descends because consecutive differentials compose to zero. -/
def cokernelDifferential (d₀ : C₀ →ₗ[R] C₁) (d₁ : C₁ →ₗ[R] C₂)
    (hd : d₁.comp d₀ = 0) : (C₁ ⧸ LinearMap.range d₀) →ₗ[R] C₂ :=
  (LinearMap.range d₀).liftQ d₁ (by
    rintro _ ⟨c, rfl⟩
    exact DFunLike.congr_fun hd c)

@[simp] theorem cokernelDifferential_mk (d₀ : C₀ →ₗ[R] C₁)
    (d₁ : C₁ →ₗ[R] C₂) (hd : d₁.comp d₀ = 0) (c : C₁) :
    cokernelDifferential d₀ d₁ hd ((LinearMap.range d₀).mkQ c) = d₁ c := rfl

/-- At the cokernel, the `d h₀` term of a homotopy vanishes and the other term
factors through the degree-two module. This is equation (C4) of the source. -/
theorem cokernel_error_factorization
    (dC : C₀ →ₗ[R] C₁) (dC' : C₁ →ₗ[R] C₂) (dT : T₀ →ₗ[R] T₁)
    (hdC : dC'.comp dC = 0)
    (φ₀ : T₀ →ₗ[R] C₀) (φ₁ : T₁ →ₗ[R] C₁)
    (ψ₀ : C₀ →ₗ[R] T₀) (ψ₁ : C₁ →ₗ[R] T₁)
    (hφ : φ₁.comp dT = dC.comp φ₀)
    (hψ : ψ₁.comp dC = dT.comp ψ₀)
    (h₀ : C₁ →ₗ[R] C₀) (h₁ : C₂ →ₗ[R] C₁)
    (hh : LinearMap.id - φ₁.comp ψ₁ = dC.comp h₀ + h₁.comp dC') :
    LinearMap.id - (cokernelMap dT dC φ₀ φ₁ hφ).comp
      (cokernelMap dC dT ψ₀ ψ₁ hψ) =
    ((LinearMap.range dC).mkQ.comp h₁).comp (cokernelDifferential dC dC' hdC) := by
  apply LinearMap.ext
  intro c
  refine Submodule.Quotient.induction_on _ c ?_
  intro c
  change (LinearMap.range dC).mkQ c -
      (LinearMap.range dC).mkQ (φ₁ (ψ₁ c)) =
    (LinearMap.range dC).mkQ (h₁ (dC' c))
  have hc := DFunLike.congr_fun hh c
  change c - φ₁ (ψ₁ c) = dC (h₀ c) + h₁ (dC' c) at hc
  rw [← map_sub, hc, map_add]
  have hz : (LinearMap.range dC).mkQ (dC (h₀ c)) = 0 := by
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨h₀ c, rfl⟩
  rw [hz, zero_add]

variable {T₂ : Type v} [AddCommGroup T₂] [Module R T₂]

/-- The stable-cokernel conclusion directly from the two degree-one homotopy
identities. Freeness of finite projectives is displayed as an auxiliary ring
hypothesis and must be proved for the Laurent ring in the final theorem. -/
theorem exists_stableFreeEquiv_of_homotopy
    (dC : C₀ →ₗ[R] C₁) (dC' : C₁ →ₗ[R] C₂)
    (dT : T₀ →ₗ[R] T₁) (dT' : T₁ →ₗ[R] T₂)
    (hdC : dC'.comp dC = 0) (hdT : dT'.comp dT = 0)
    (φ₀ : T₀ →ₗ[R] C₀) (φ₁ : T₁ →ₗ[R] C₁)
    (ψ₀ : C₀ →ₗ[R] T₀) (ψ₁ : C₁ →ₗ[R] T₁)
    (hφ : φ₁.comp dT = dC.comp φ₀)
    (hψ : ψ₁.comp dC = dT.comp ψ₀)
    (hC₀ : C₁ →ₗ[R] C₀) (hC₁ : C₂ →ₗ[R] C₁)
    (hT₀ : T₁ →ₗ[R] T₀) (hT₁ : T₂ →ₗ[R] T₁)
    (hhC : LinearMap.id - φ₁.comp ψ₁ = dC.comp hC₀ + hC₁.comp dC')
    (hhT : LinearMap.id - ψ₁.comp φ₁ = dT.comp hT₀ + hT₁.comp dT')
    [Module.Finite R C₂] [Module.Free R C₂]
    [Module.Finite R T₂] [Module.Projective R T₂]
    (hfree : ∀ (L : Type v) [AddCommGroup L] [Module R L]
      [Module.Finite R L] [Module.Projective R L], Module.Free R L) :
    ∃ a b : ℕ, Nonempty
      (((T₁ ⧸ LinearMap.range dT) × (Fin b → R)) ≃ₗ[R]
        ((C₁ ⧸ LinearMap.range dC) × (Fin a → R))) :=
  exists_stableFreeEquiv
    (cokernelMap dC dT ψ₀ ψ₁ hψ) (cokernelMap dT dC φ₀ φ₁ hφ)
    (cokernelDifferential dC dC' hdC) ((LinearMap.range dC).mkQ.comp hC₁)
    (cokernelDifferential dT dT' hdT) ((LinearMap.range dT).mkQ.comp hT₁)
    (cokernel_error_factorization dC dC' dT hdC φ₀ φ₁ ψ₀ ψ₁ hφ hψ hC₀ hC₁ hhC)
    (cokernel_error_factorization dT dT' dC hdT ψ₀ ψ₁ φ₀ φ₁ hψ hφ hT₀ hT₁ hhT)
    hfree

end Decoupling.HighDim.StableCokernel
