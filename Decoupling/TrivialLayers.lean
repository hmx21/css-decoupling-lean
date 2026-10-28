import Decoupling.LayerTranslations
import Decoupling.EvaluationLinear
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Finite layers with trivial translations

For an actual Laurent-ring module, trivial action of every Laurent monomial
forces the entire scalar action to factor through evaluation at `(1,1,1)`.
A finite basis of its coefficient-field vector space then gives an actual
`R`-linear equivalence with `Trivial t`, where `t` is its genuine finite rank.
The layer identification is constructed, not assumed.
-/

universe u

namespace Decoupling.TrivialLayers

open Module LayerTranslations EvaluationLinear

noncomputable section

variable (M : ModuleCat.{u} R)

/-- The translation-triviality hypothesis on the actual module action. -/
def TranslationsTrivial : Prop := ∀ a : Translation, ∀ m : M, monomial a • m = m

/-- Trivial Laurent translations force every scalar to act through augmentation. -/
theorem scalar_factors (hM : TranslationsTrivial M) (r : R) (m : M) :
    r • m = constant (augmentation r) • m := by
  refine AddMonoidAlgebra.induction_on
    (motive := fun r : R => r • m = constant (augmentation r) • m) r ?_ ?_ ?_
  · intro a
    change monomial a • m = constant (augmentation (monomial a)) • m
    rw [augmentation_monomial, map_one, one_smul]
    exact hM a m
  · intro r s hr hs
    rw [map_add, map_add, add_smul, add_smul, hr, hs]
  · intro a r hr
    have ha : a = 0 ∨ a = 1 := by
      fin_cases a
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases ha with rfl | rfl
    · simp
    · simpa using hr

/-- The same identity in the canonical coefficient-field module. -/
theorem scalar_factors_coefficients (hM : TranslationsTrivial M) (r : R) (m : M) :
    (show coefficients M from r • m) =
      augmentation r • (show coefficients M from m) := scalar_factors M hM r m

/-- The augmentation ideal annihilates the layer, as required for the Koszul comparison. -/
theorem ideal_annihilates (hM : TranslationsTrivial M) (r : R) (hr : r ∈ J) (m : M) :
    r • m = 0 := by
  have hzero : augmentation r = 0 := by
    rw [← ker_augmentation_eq_J] at hr
    exact hr
  rw [scalar_factors M hM r m, hzero, map_zero, zero_smul]

variable [FiniteDimensional (ZMod 2) (coefficients M)]

/-- The actual finite-dimensional layer, with its original `R` action, is the
trivial translation module of dimension `finrank 𝔽₂ M`. -/
def equivTrivial (hM : TranslationsTrivial M) :
    M ≃ₗ[R] Trivial (Module.finrank (ZMod 2) (coefficients M)) := by
  let e := (Module.finBasis (ZMod 2) (coefficients M)).equivFun
  exact {
    toFun := fun m => e (show coefficients M from m)
    invFun := fun v => (show M from e.symm v)
    left_inv := fun m => e.symm_apply_apply m
    right_inv := fun v => e.apply_symm_apply v
    map_add' := fun m n => e.map_add m n
    map_smul' := by
      intro r m
      change e (show coefficients M from r • m) = augmentation r • e m
      rw [scalar_factors_coefficients M hM]
      exact e.map_smul _ _
  }

/-- Explicit existence form, without an input isomorphism to the standard layer. -/
theorem exists_equivTrivial (hM : TranslationsTrivial M) :
    Nonempty (M ≃ₗ[R] Trivial (Module.finrank (ZMod 2) (coefficients M))) :=
  ⟨equivTrivial M hM⟩

end

end Decoupling.TrivialLayers
