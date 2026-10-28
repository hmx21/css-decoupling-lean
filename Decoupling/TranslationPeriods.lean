import Decoupling.LayerTranslations
import Mathlib.GroupTheory.OrderOfElement

/-! A common rectangular retained lattice for the actual finite Ext layers. -/

namespace Decoupling.TranslationPeriods

open FiniteTranslations LayerTranslations

/-- A common positive period can be chosen in all coordinate directions.
Thus the first retained lattice can be nℤ³, before the further doubling. -/
theorem exists_common_period
    {E₁ E₂ : Type*}
    [AddCommGroup E₁] [Module (ZMod 2) E₁] [FiniteDimensional (ZMod 2) E₁]
    [AddCommGroup E₂] [Module (ZMod 2) E₂] [FiniteDimensional (ZMod 2) E₂]
    (ρ₁ : TranslationGroup →* (E₁ ≃ₗ[ZMod 2] E₁))
    (ρ₂ : TranslationGroup →* (E₂ ≃ₗ[ZMod 2] E₂)) :
    ∃ n : ℕ, 0 < n ∧ ∀ a : Translation,
      ρ₁ (Multiplicative.ofAdd (n • a)) = 1 ∧
      ρ₂ (Multiplicative.ofAdd (n • a)) = 1 := by
  let : Finite E₁ := Module.finite_of_finite (ZMod 2)
  let : Finite E₂ := Module.finite_of_finite (ZMod 2)
  let : Finite (E₁ ≃ₗ[ZMod 2] E₁) :=
    Finite.of_injective (fun e : E₁ ≃ₗ[ZMod 2] E₁ => (e : E₁ → E₁))
      DFunLike.coe_injective
  let : Finite (E₂ ≃ₗ[ZMod 2] E₂) :=
    Finite.of_injective (fun e : E₂ ≃ₗ[ZMod 2] E₂ => (e : E₂ → E₂))
      DFunLike.coe_injective
  let G := (E₁ ≃ₗ[ZMod 2] E₁) × (E₂ ≃ₗ[ZMod 2] E₂)
  refine ⟨Nat.card G, Nat.card_pos, ?_⟩
  intro a
  have h : (ρ₁.prod ρ₂) ((Multiplicative.ofAdd a) ^ Nat.card G) = 1 := by
    rw [map_pow]
    exact pow_card_eq_one'
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-- Only the manuscript's finite-layer assumptions enter this actual Ext version. -/
theorem exists_layer_period {q s r : ℕ} (c : CSS.Checks q s r)
    [FiniteDimensional (ZMod 2) (coefficients (layer c 1))]
    [FiniteDimensional (ZMod 2) (coefficients (layer c 2))] :
    ∃ n : ℕ, 0 < n ∧ ∀ a : Translation,
      representation (layer c 1) (Multiplicative.ofAdd (n • a)) = 1 ∧
      representation (layer c 2) (Multiplicative.ofAdd (n • a)) = 1 :=
  exists_common_period (representation (layer c 1)) (representation (layer c 2))

end Decoupling.TranslationPeriods
