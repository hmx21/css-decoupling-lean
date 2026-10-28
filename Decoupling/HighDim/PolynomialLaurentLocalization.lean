import Decoupling.HighDim.PolynomialLaurentClearing
import Mathlib.RingTheory.Localization.Defs

/-!
# HD014 actual Laurent localization at the polynomial monomials

The coefficient inclusion into the real translation group algebra satisfies
the native IsLocalization universal property. Denominators are genuine
D-variable monomials; no quotient exactness is assumed.
-/
namespace Decoupling.HighDim.PolynomialLaurent
noncomputable section
variable (D : ℕ) (K : Type*) [CommRing K]

def positiveMonomials : Submonoid (Poly D K) where
  carrier := Set.range (fun a : Exponent D => MvPolynomial.monomial a (1 : K))
  one_mem' := ⟨0,rfl⟩
  mul_mem' := by
    rintro p q ⟨a,rfl⟩ ⟨b,rfl⟩
    exact ⟨a+b,by simp [MvPolynomial.monomial_mul_monomial]⟩

instance polynomialAlgebra : Algebra (Poly D K) (Laurent K D) := (inclusion D K).toAlgebra

theorem algebraMap_eq : algebraMap (Poly D K) (Laurent K D) = inclusion D K := rfl

def diagonalExponent (h : ℕ) : Exponent D := Finsupp.equivFunOnFinite.symm (fun _ => h)

theorem exponentMap_diagonal (h : ℕ) :
    exponentMap D (diagonalExponent D h) = constantExponent D h := by
  funext i
  rfl

def denominator (h : ℕ) : positiveMonomials D K :=
  ⟨MvPolynomial.monomial (diagonalExponent D h) 1,⟨diagonalExponent D h,rfl⟩⟩

theorem denominator_image (h : ℕ) :
    inclusion D K (denominator D K h).val = monomial K (constantExponent D h) := by
  change inclusion D K (MvPolynomial.monomial _ _) = _
  rw [inclusion_monomial,exponentMap_diagonal]
  rfl

instance isLocalization : IsLocalization (positiveMonomials D K) (Laurent K D) := by
  apply (isLocalization_iff (positiveMonomials D K) (Laurent K D)).mpr
  refine ⟨?_,?_,?_⟩
  · intro y
    obtain ⟨a,ha⟩ := y.property
    change IsUnit (inclusion D K y.val)
    rw [←ha]
    exact inclusion_monomial_one_unit D K a
  · intro f
    refine ⟨(clear f (supportRadius f),denominator D K (supportRadius f)),?_⟩
    change f*inclusion D K (denominator D K (supportRadius f)).val =
      inclusion D K (clear f (supportRadius f))
    rw [denominator_image,clear_correct f _ (supported_radius f),mul_comm]
  · intro x y he
    have hxy : x=y := inclusion_injective D K he
    exact ⟨1,by simp only [hxy]⟩

end
end Decoupling.HighDim.PolynomialLaurent
