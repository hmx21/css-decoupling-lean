import Decoupling.HighDim.LaurentBoxes
import Mathlib.Algebra.MvPolynomial.Basic

/-!
# HD014 the genuine D-variable polynomial subring of the Laurent ring

This is the injective positive-exponent inclusion. It is distinct from
the 2D-variable quotient presentation used by the linear solver.
-/
namespace Decoupling.HighDim.PolynomialLaurent
noncomputable section
variable (D : ℕ)

abbrev Exponent := Fin D →₀ ℕ
abbrev Poly (K : Type*) [CommRing K] := MvPolynomial (Fin D) K

def exponentMap : Exponent D →+ Translation D where
  toFun a i := (a i : ℤ)
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp

theorem exponentMap_injective : Function.Injective (exponentMap D) := by
  intro a b h
  ext i
  have he := congrFun h i
  change (a i : ℤ) = (b i : ℤ) at he
  exact_mod_cast he

variable (K : Type*) [CommRing K]

def inclusion : Poly D K →+* Laurent K D :=
  AddMonoidAlgebra.mapDomainRingHom K (exponentMap D)

theorem inclusion_injective : Function.Injective (inclusion D K) :=
  AddMonoidAlgebra.mapDomain_injective (exponentMap_injective D)

@[simp] theorem inclusion_monomial (a : Exponent D) (c : K) :
    inclusion D K (MvPolynomial.monomial a c) =
      AddMonoidAlgebra.single (exponentMap D a) c := by
  simp [inclusion,MvPolynomial.monomial]

@[simp] theorem inclusion_C (c : K) :
    inclusion D K (MvPolynomial.C c) = constant c := by
  change inclusion D K (MvPolynomial.monomial 0 c) = _
  rw [inclusion_monomial,map_zero]
  rfl

@[simp] theorem inclusion_X (i : Fin D) :
    inclusion D K (MvPolynomial.X i) = coordinate K i := by
  rw [MvPolynomial.X,inclusion_monomial]
  congr 1
  funext j
  by_cases hj : j=i <;> simp [exponentMap,translationBasis,hj]

theorem inclusion_monomial_one_unit (a : Exponent D) :
    IsUnit (inclusion D K (MvPolynomial.monomial a 1)) := by
  rw [inclusion_monomial]
  refine ⟨⟨monomial K (exponentMap D a),monomial K (-(exponentMap D a)),?_,?_⟩,rfl⟩
  · exact monomial_mul_neg _
  · exact monomial_neg_mul _

end
end Decoupling.HighDim.PolynomialLaurent
