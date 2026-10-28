import Decoupling.HighDim.LaurentPresentation
import Decoupling.HighDim.LaurentBoxes
import Mathlib.Algebra.MvPolynomial.Degrees

/-! # HD012 canonical polynomial lifts, their exact images and degree bounds -/
namespace Decoupling.HighDim.LaurentPresentation
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (D : ℕ)

def liftExponent (a : Translation D) : (Fin D ⊕ Fin D) →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Sum.elim (fun i => (a i).toNat) (fun i => (-a i).toNat))

@[simp] theorem exponentMap_liftExponent (a : Translation D) :
    exponentMap D (liftExponent D a) = a := by
  funext i
  change (((a i).toNat : ℕ) : ℤ) - (((-a i).toNat : ℕ) : ℤ) = a i
  omega

theorem liftExponent_sum_le (a : Translation D) (h : ℕ) (ha : a ∈ LaurentBoxes.box D h) :
    (liftExponent D a).sum (fun _ n => n) ≤ (2 * D) * h := by
  rw [Finsupp.sum_fintype _ _ (by simp)]
  calc
    _ ≤ ∑ _i : Fin D ⊕ Fin D, h := by
      apply Finset.sum_le_sum
      intro i _
      have hh := (LaurentBoxes.mem_box a).mp ha
      cases i with
      | inl i => change (a i).toNat ≤ h; have := hh i; omega
      | inr i => change (-a i).toNat ≤ h; have := hh i; omega
    _ = _ := by simp [two_mul]

variable (K : Type*) [CommRing K]

/-- Lift each integer exponent to its positive and negative parts. This
is an explicit finite polynomial expression, not an inverse ring homomorphism. -/
def liftPolynomial (f : Laurent K D) : Poly K D :=
  f.coeff.sum (fun a c => MvPolynomial.monomial (liftExponent D a) c)

@[simp] theorem evaluate_liftPolynomial (f : Laurent K D) :
    evaluate K D (liftPolynomial D K f) = f := by
  rw [liftPolynomial, map_finsuppSum]
  simp only [evaluate_monomial, exponentMap_liftExponent]
  exact AddMonoidAlgebra.sum_coeff_single f

theorem evaluate_surjective : Function.Surjective (evaluate K D) :=
  fun f => ⟨liftPolynomial D K f, evaluate_liftPolynomial D K f⟩

theorem liftPolynomial_degree (f : Laurent K D) (h : ℕ) (hf : LaurentBoxes.Supported f h) :
    (liftPolynomial D K f).totalDegree ≤ 2 * D * h := by
  change (∑ a ∈ f.coeff.support, MvPolynomial.monomial (liftExponent D a) (f.coeff a)).totalDegree ≤ _
  apply MvPolynomial.totalDegree_finsetSum_le
  intro a ha
  exact (MvPolynomial.totalDegree_monomial_le _ _).trans (liftExponent_sum_le D a h (hf ha))

/-- The original Laurent ring is exactly the polynomial presentation by
the inverse relations, with a proved surjection and exact kernel. -/
def quotientEquiv : QuotientRing K D ≃+* Laurent K D :=
  (Ideal.quotEquivOfEq (kernel_evaluate K D).symm).trans
    ((evaluate K D).quotientKerEquivOfSurjective (evaluate_surjective D K))

end
end Decoupling.HighDim.LaurentPresentation
