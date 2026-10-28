import Decoupling.ExtLayers
import Decoupling.Augmentation
import Decoupling.FiniteTranslations

/-!
# Finite retained translations for the actual Ext layers

This connects Proposition I.2 to the genuine modules E_X^i defined in
`ExtLayers`. The action is multiplication by Laurent monomials. The scalar
field acts through constant Laurent polynomials; no arbitrary representation
or replacement for the Ext layers is supplied as an additional input.
-/

namespace Decoupling.LayerTranslations

open CategoryTheory

noncomputable section

/-- Forget an R-module down to its coefficient-field vector space. -/
def coefficients (M : ModuleCat R) : ModuleCat (ZMod 2) :=
  (ModuleCat.restrictScalars constant).obj M

/-- Translation by a, acting on the coefficient-field vector space of any R-module. -/
def translationEquiv (M : ModuleCat R) (a : Translation) :
    coefficients M ≃ₗ[ZMod 2] coefficients M where
  toFun m := monomial a • (show M from m)
  invFun m := monomial (-a) • (show M from m)
  left_inv m := by
    change monomial (-a) • (monomial a • (show M from m)) = m
    rw [← mul_smul, monomial_neg_mul, one_smul]
  right_inv m := by
    change monomial a • (monomial (-a) • (show M from m)) = m
    rw [← mul_smul, monomial_mul_neg, one_smul]
  map_add' m n := by
    change monomial a • ((show M from m) + (show M from n)) =
      monomial a • (show M from m) + monomial a • (show M from n)
    exact smul_add _ _ _
  map_smul' r m := by
    change monomial a • (constant r • (show M from m)) =
      constant r • (monomial a • (show M from m))
    exact smul_comm _ _ _

/-- The canonical ℤ³ representation induced by Laurent multiplication. -/
def representation (M : ModuleCat R) :
    FiniteTranslations.TranslationGroup →* (coefficients M ≃ₗ[ZMod 2] coefficients M) where
  toFun a := translationEquiv M a.toAdd
  map_one' := by
    ext m
    change monomial 0 • (show M from m) = m
    rw [monomial_zero]
    exact one_smul R (show M from m)
  map_mul' a b := by
    ext m
    change monomial (a.toAdd + b.toAdd) • (show M from m) =
      monomial a.toAdd • (monomial b.toAdd • (show M from m))
    rw [← monomial_mul, mul_smul]

variable {q s r : ℕ}

/-- Genuine Ext_R^i(overline M_X,R), bundled with its canonical R-module structure. -/
def layer (c : CSS.Checks q s r) (i : ℕ) : ModuleCat R :=
  ModuleCat.of R (ExtLayers.E_X c i)

/-- Proposition I.2 for the actual Ext layers, with just Assumption 2 as input. -/
theorem exists_retained_translations (c : CSS.Checks q s r)
    [FiniteDimensional (ZMod 2) (coefficients (layer c 1))]
    [FiniteDimensional (ZMod 2) (coefficients (layer c 2))] :
    ∃ Λ : Subgroup FiniteTranslations.TranslationGroup,
      Λ.FiniteIndex ∧ ∀ a ∈ Λ,
        (∀ e : coefficients (layer c 1), representation (layer c 1) a e = e) ∧
        (∀ e : coefficients (layer c 2), representation (layer c 2) a e = e) :=
  FiniteTranslations.exists_retained_subgroup_fixing_elements
    (representation (layer c 1)) (representation (layer c 2))

end
end Decoupling.LayerTranslations
