import Decoupling.ScalarExtensionDimension
import Decoupling.Laurent
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Algebra.Field.ZMod

/-!
# The three-variable Laurent projective-dimension bound

The proof starts with modules over the field, applies the proved Laurent
extension sequence three times, and transports along the explicit ring
equivalence from the paper's translation group algebra. No global-dimension
or Laurent-projective freeness theorem is assumed here.
-/

namespace Decoupling.LaurentGlobalDimension

open scoped TensorProduct LaurentPolynomial
open CategoryTheory CategoryTheory.Abelian

noncomputable section

universe u

variable {A : Type u} [CommRing A]

/-- Adding one Laurent variable raises a uniform native projective-dimension
bound by at most one. -/
theorem laurent_bound (n : ℕ)
    (hA : ∀ N : ModuleCat.{u} A, HasProjectiveDimensionLE N n)
    (M : ModuleCat.{u} A[T;T⁻¹]) : HasProjectiveDimensionLE M (n + 1) := by
  let : Module A M := Module.compHom M (algebraMap A A[T;T⁻¹])
  let : IsScalarTower A A[T;T⁻¹] M :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let : Module.Free A A[T;T⁻¹] := Module.Free.of_basis (AddMonoidAlgebra.basis ℤ A)
  have : HasProjectiveDimensionLE (ModuleCat.of A M) n := hA (ModuleCat.of A M)
  have : HasProjectiveDimensionLE (ModuleCat.of A[T;T⁻¹] (A[T;T⁻¹] ⊗[A] M)) n :=
    ScalarExtensionDimension.tensor_projectiveDimensionLE n (ModuleCat.of A M)
  exact LaurentInduction.projectiveDimensionLE_succ (A := A) (M := M) n

/-- The iterated Laurent rings used only to calculate the dimension. -/
abbrev Laurent₁ := LaurentPolynomial (ZMod 2)
abbrev Laurent₂ := LaurentPolynomial Laurent₁
abbrev Laurent₃ := LaurentPolynomial Laurent₂

theorem field_bound (M : ModuleCat.{0} (ZMod 2)) : HasProjectiveDimensionLE M 0 := by
  have : Module.Free (ZMod 2) M := inferInstance
  have : Module.Projective (ZMod 2) M := inferInstance
  exact (projective_iff_hasProjectiveDimensionLE_zero M).mp inferInstance

theorem one_variable_bound (M : ModuleCat.{0} Laurent₁) : HasProjectiveDimensionLE M 1 :=
  laurent_bound 0 field_bound M

theorem two_variable_bound (M : ModuleCat.{0} Laurent₂) : HasProjectiveDimensionLE M 2 :=
  laurent_bound 1 one_variable_bound M

theorem three_variable_bound (M : ModuleCat.{0} Laurent₃) : HasProjectiveDimensionLE M 3 :=
  laurent_bound 2 two_variable_bound M

/-- The ordered translation coordinates are kept as `(x,(y,z))`. -/
def translationProduct : (Fin 3 → ℤ) ≃+ ℤ × (ℤ × ℤ) where
  toFun a := (a 0, a 1, a 2)
  invFun a := ![a.1, a.2.1, a.2.2]
  left_inv a := by funext i; fin_cases i <;> rfl
  right_inv a := rfl
  map_add' a b := rfl

/-- Explicitly identifies the actual paper ring with three successive
Laurent extensions, in the order x outside y outside z. -/
def iteratedLaurentEquiv : R ≃+* Laurent₃ :=
  (AddMonoidAlgebra.mapDomainRingEquiv (ZMod 2) translationProduct).trans
    ((AddMonoidAlgebra.curryRingEquiv :
      AddMonoidAlgebra (ZMod 2) (ℤ × (ℤ × ℤ)) ≃+*
        AddMonoidAlgebra (AddMonoidAlgebra (ZMod 2) (ℤ × ℤ)) ℤ).trans
      (AddMonoidAlgebra.mapRingEquiv ℤ
        (AddMonoidAlgebra.curryRingEquiv :
          AddMonoidAlgebra (ZMod 2) (ℤ × ℤ) ≃+* Laurent₂)))

/-- Every module over the paper's actual Laurent ring has native projective
dimension at most three. No finiteness hypothesis on the module is needed. -/
theorem laurent_global_bound (M : ModuleCat.{0} R) : HasProjectiveDimensionLE M 3 := by
  let e := ModuleCat.restrictScalarsEquivalenceOfRingEquiv (R := R) (S := Laurent₃)
    iteratedLaurentEquiv
  have : HasProjectiveDimensionLE (e.inverse.obj M) 3 :=
    three_variable_bound (e.inverse.obj M)
  have hF : HasProjectiveDimensionLE (e.functor.obj (e.inverse.obj M)) 3 :=
    ScalarExtensionDimension.functor_projectiveDimensionLE e.functor 3 (e.inverse.obj M)
  exact @hasProjectiveDimensionLT_of_iso _ _ _ _ _ (e.counitIso.app M) 4 hF

end

end Decoupling.LaurentGlobalDimension
