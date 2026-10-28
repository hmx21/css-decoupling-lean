import Decoupling.GeneralRetained
import Decoupling.TranslationPeriods
import Decoupling.TrivialLayers

/-!
# Actual finite layers after the first retained period

Restriction along the nth-power embedding is restriction to the literal
retained subring followed by renaming its generators. Coefficient vector
spaces and their dimensions are preserved. This concerns restricted modules;
identifying them with Ext of the restricted CSS presentation is a separate
duality theorem, not built into these definitions.
-/

namespace Decoupling.RetainedLayers

open LayerTranslations EvaluationLinear

noncomputable section

def restricted (n : ℕ) (M : ModuleCat R) : ModuleCat R :=
  (ModuleCat.restrictScalars (GeneralRetained.embed n)).obj M

theorem embed_constant (n : ℕ) (r : ZMod 2) :
    GeneralRetained.embed n (constant r) = constant r := by
  simp [GeneralRetained.embed, constant]

/-- Retaining cells changes the translation action but not the coefficient space. -/
def coefficientEquiv (n : ℕ) (M : ModuleCat R) :
    coefficients (restricted n M) ≃ₗ[ZMod 2] coefficients M where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r m := by
    change GeneralRetained.embed n (constant r) • (show M from m) = constant r • (show M from m)
    rw [embed_constant]

instance (n : ℕ) (M : ModuleCat R)
    [FiniteDimensional (ZMod 2) (coefficients M)] :
    FiniteDimensional (ZMod 2) (coefficients (restricted n M)) :=
  Module.Finite.equiv (coefficientEquiv n M).symm

theorem restricted_finrank (n : ℕ) (M : ModuleCat R) :
    Module.finrank (ZMod 2) (coefficients (restricted n M)) =
      Module.finrank (ZMod 2) (coefficients M) := (coefficientEquiv n M).finrank_eq

theorem trivial_of_period (n : ℕ) (M : ModuleCat R)
    (h : ∀ a : Translation, representation M (Multiplicative.ofAdd (n • a)) = 1) :
    TrivialLayers.TranslationsTrivial (restricted n M) := by
  intro a m
  change GeneralRetained.embed n (monomial a) • (show M from m) = m
  have he : GeneralRetained.embed n (monomial a) = monomial (n • a) := by
    simp only [GeneralRetained.embed, monomial, AddMonoidAlgebra.mapDomainRingHom_apply,
      AddMonoidAlgebra.mapDomain_single]
    congr 1
  rw [he]
  exact DFunLike.congr_fun (h a) (show coefficients M from m)

def equivTrivialOfPeriod (n : ℕ) (M : ModuleCat R)
    [FiniteDimensional (ZMod 2) (coefficients M)]
    (h : ∀ a : Translation, representation M (Multiplicative.ofAdd (n • a)) = 1) :
    restricted n M ≃ₗ[R] Trivial (Module.finrank (ZMod 2) (coefficients M)) := by
  rw [← restricted_finrank n M]
  exact TrivialLayers.equivTrivial (restricted n M) (trivial_of_period n M h)

/-- Both actual finite Ext layers become trivial at one common positive period,
with unchanged coefficient dimensions. This includes zero-dimensional layers. -/
theorem exists_trivial_retained_layers {q s r : ℕ} (c : CSS.Checks q s r)
    [FiniteDimensional (ZMod 2) (coefficients (layer c 1))]
    [FiniteDimensional (ZMod 2) (coefficients (layer c 2))] :
    ∃ n : ℕ, 0 < n ∧
      Nonempty (restricted n (layer c 1) ≃ₗ[R]
        Trivial (Module.finrank (ZMod 2) (coefficients (layer c 1)))) ∧
      Nonempty (restricted n (layer c 2) ≃ₗ[R]
        Trivial (Module.finrank (ZMod 2) (coefficients (layer c 2)))) := by
  obtain ⟨n, hn, h⟩ := TranslationPeriods.exists_layer_period c
  exact ⟨n, hn, ⟨equivTrivialOfPeriod n (layer c 1) (fun a => (h a).1)⟩,
    ⟨equivTrivialOfPeriod n (layer c 2) (fun a => (h a).2)⟩⟩

end
end Decoupling.RetainedLayers
