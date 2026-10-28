import Decoupling.HighDim.Laurent
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Tactic.Ring

/-!
# The augmentation quotient in arbitrary dimension and characteristic

Source: `drafts/main.tex` Section II.B and equation (15).
The equality ker(augmentation) = (x_i-1) is proved for integer Laurent
exponents, including negative powers. No finite-dimensional module or
Koszul exactness hypothesis is used.
-/

namespace Decoupling.HighDim
noncomputable section

variable {K : Type*} [CommRing K] {D : ℕ}

def monomialCongruenceExponents (I : Ideal (Laurent K D)) : AddSubgroup (Translation D) where
  carrier := {a | monomial K a - 1 ∈ I}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change monomial K (a + b) - 1 ∈ I
    rw [← monomial_mul]
    convert I.add_mem (I.mul_mem_left (monomial K a) hb) ha using 1
    ring
  neg_mem' := by
    intro a ha
    change monomial K (-a) - 1 ∈ I
    simpa only [mul_sub, monomial_neg_mul, mul_one, neg_sub] using
      I.neg_mem (I.mul_mem_left (monomial K (-a)) ha)

theorem monomial_sub_one_mem_augmentationIdeal (a : Translation D) :
    monomial K a - 1 ∈ augmentationIdeal K D := by
  let G := monomialCongruenceExponents (augmentationIdeal K D)
  have hb (i : Fin D) : translationBasis i ∈ G := difference_mem_augmentationIdeal i
  have ha : a = ∑ i : Fin D, a i • translationBasis i := by
    funext i
    simp [translationBasis, Finset.sum_apply, Pi.single_apply]
  change a ∈ G
  rw [ha]
  exact G.sum_mem (fun i _ => G.zsmul_mem (hb i) (a i))

theorem sub_constant_augmentation_mem (f : Laurent K D) :
    f - constant (augmentation f) ∈ augmentationIdeal K D := by
  refine AddMonoidAlgebra.induction_on
    (motive := fun g : Laurent K D =>
      g - constant (augmentation g) ∈ augmentationIdeal K D) f ?_ ?_ ?_
  · intro a
    change monomial K a - constant (augmentation (monomial K a)) ∈ _
    simpa only [augmentation_monomial, map_one] using
      monomial_sub_one_mem_augmentationIdeal (K := K) a
  · intro f g hf hg
    rw [map_add, map_add]
    convert (augmentationIdeal K D).add_mem hf hg using 1
    ring
  · intro c f hf
    have hc : c • f = constant c * f := by
      change c • f = AddMonoidAlgebra.single 0 c * f
      ext a
      simp
    rw [hc, map_mul, augmentation_constant, map_mul]
    rw [← mul_sub]
    exact (augmentationIdeal K D).mul_mem_left (constant c) hf

theorem ker_augmentation_eq :
    RingHom.ker (augmentation : Laurent K D →+* K) = augmentationIdeal K D := by
  apply le_antisymm ?_ augmentationIdeal_le_ker
  intro f hf
  have hfzero := RingHom.mem_ker.mp hf
  simpa [hfzero] using sub_constant_augmentation_mem f

def augmentationQuotientEquiv : Laurent K D ⧸ augmentationIdeal K D ≃+* K :=
  (Ideal.quotEquivOfEq ker_augmentation_eq.symm).trans
    (augmentation.quotientKerEquivOfSurjective augmentation_surjective)

@[simp] theorem augmentationQuotientEquiv_mk (f : Laurent K D) :
    augmentationQuotientEquiv (Ideal.Quotient.mk (augmentationIdeal K D) f) =
      augmentation f := by
  simp [augmentationQuotientEquiv]

end
end Decoupling.HighDim
