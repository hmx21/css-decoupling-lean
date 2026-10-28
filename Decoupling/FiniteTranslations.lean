import Mathlib.Algebra.Field.ZMod
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# Finite layers and retained translations

This file proves Proposition I.2 of `notes/main.pdf`. The translation group
is the additive lattice `ℤ³`, written as `Multiplicative (Fin 3 → ℤ)` solely
to use group homomorphisms into groups of linear automorphisms. Its group
multiplication is therefore addition of lattice vectors, not coordinatewise
multiplication of integers.

The two layers are supplied as finite-dimensional vector spaces over `𝔽₂`,
together with their translation representations. No positive-dimension
assumption is made, so the statement includes either or both zero layers.
Identifying these supplied spaces and actions with the manuscript's Ext
modules is a separate homological obligation.
-/

namespace Decoupling

namespace FiniteTranslations

/-- The manuscript's lattice `ℤ³`, written multiplicatively for representations. -/
abbrev TranslationGroup := Multiplicative (Fin 3 → ℤ)

/-- Proposition I.2: finite-dimensional `𝔽₂` layers have a common finite-index
subgroup of translations acting trivially on both layers. The subgroup is the
kernel of the product of their two translation representations. -/
theorem exists_retained_subgroup
    {E₁ E₂ : Type*}
    [AddCommGroup E₁] [Module (ZMod 2) E₁] [FiniteDimensional (ZMod 2) E₁]
    [AddCommGroup E₂] [Module (ZMod 2) E₂] [FiniteDimensional (ZMod 2) E₂]
    (ρ₁ : TranslationGroup →* (E₁ ≃ₗ[ZMod 2] E₁))
    (ρ₂ : TranslationGroup →* (E₂ ≃ₗ[ZMod 2] E₂)) :
    ∃ Λ : Subgroup TranslationGroup,
      Λ.FiniteIndex ∧ ∀ a ∈ Λ, ρ₁ a = 1 ∧ ρ₂ a = 1 := by
  let : Finite E₁ := Module.finite_of_finite (ZMod 2)
  let : Finite E₂ := Module.finite_of_finite (ZMod 2)
  let : Finite (E₁ ≃ₗ[ZMod 2] E₁) :=
    Finite.of_injective (fun e : E₁ ≃ₗ[ZMod 2] E₁ => (e : E₁ → E₁))
      DFunLike.coe_injective
  let : Finite (E₂ ≃ₗ[ZMod 2] E₂) :=
    Finite.of_injective (fun e : E₂ ≃ₗ[ZMod 2] E₂ => (e : E₂ → E₂))
      DFunLike.coe_injective
  refine ⟨(ρ₁.prod ρ₂).ker, inferInstance, ?_⟩
  intro a ha
  have h : (ρ₁.prod ρ₂) a = 1 := MonoidHom.mem_ker.mp ha
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- The pointwise form of Proposition I.2: every retained translation fixes
every element of each layer. -/
theorem exists_retained_subgroup_fixing_elements
    {E₁ E₂ : Type*}
    [AddCommGroup E₁] [Module (ZMod 2) E₁] [FiniteDimensional (ZMod 2) E₁]
    [AddCommGroup E₂] [Module (ZMod 2) E₂] [FiniteDimensional (ZMod 2) E₂]
    (ρ₁ : TranslationGroup →* (E₁ ≃ₗ[ZMod 2] E₁))
    (ρ₂ : TranslationGroup →* (E₂ ≃ₗ[ZMod 2] E₂)) :
    ∃ Λ : Subgroup TranslationGroup,
      Λ.FiniteIndex ∧ ∀ a ∈ Λ,
        (∀ e : E₁, ρ₁ a e = e) ∧ (∀ e : E₂, ρ₂ a e = e) := by
  obtain ⟨Λ, hΛ, hρ⟩ := exists_retained_subgroup ρ₁ ρ₂
  refine ⟨Λ, hΛ, ?_⟩
  intro a ha
  obtain ⟨h₁, h₂⟩ := hρ a ha
  constructor
  · intro e
    rw [h₁]
    rfl
  · intro e
    rw [h₂]
    rfl

end FiniteTranslations

end Decoupling
