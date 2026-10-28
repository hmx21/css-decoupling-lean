import Decoupling.Laurent
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The augmentation quotient

This file proves the assertion `R/J ≅ 𝔽₂` in Section I.C of
`notes/main.pdf`, for the concrete Laurent ring and ideal defined in
`Decoupling.Laurent`.  In particular, equality of the augmentation
kernel with `J = (x-1,y-1,z-1)` is a conclusion, not a hypothesis.

The proof first shows that every Laurent monomial is congruent to one
modulo `J`.  It uses integer, not merely nonnegative, translation
exponents, so the inverse Laurent variables are included.
-/

noncomputable section

namespace Decoupling

/-- The constant Laurent polynomial, as a ring homomorphism. -/
def constant : ZMod 2 →+* R := AddMonoidAlgebra.singleZeroRingHom

@[simp] theorem constant_apply (c : ZMod 2) :
    constant c = AddMonoidAlgebra.single 0 c := rfl

@[simp] theorem augmentation_constant (c : ZMod 2) :
    augmentation (constant c) = c := by
  simp

/-- The translation exponents whose monomials equal one modulo a given ideal. -/
def monomialCongruenceExponents (I : Ideal R) : AddSubgroup Translation where
  carrier := {a | monomial a - 1 ∈ I}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb
    change monomial (a + b) - 1 ∈ I
    rw [← monomial_mul]
    convert I.add_mem (I.mul_mem_left (monomial a) hb) ha using 1
    ring
  neg_mem' := by
    intro a ha
    change monomial (-a) - 1 ∈ I
    simpa only [mul_sub, monomial_neg_mul, mul_one, neg_sub] using
      I.neg_mem (I.mul_mem_left (monomial (-a)) ha)

@[simp] theorem mem_monomialCongruenceExponents (I : Ideal R) (a : Translation) :
    a ∈ monomialCongruenceExponents I ↔ monomial a - 1 ∈ I := Iff.rfl

private abbrev augmentationExponents := monomialCongruenceExponents J

private theorem basis_mem_augmentationExponents (i : Fin 3) :
    translationBasis i ∈ augmentationExponents := by
  fin_cases i
  · exact u_mem_J
  · exact v_mem_J
  · exact w_mem_J

/-- Every Laurent monomial, including negative exponents, equals one modulo `J`. -/
theorem monomial_sub_one_mem_J (a : Translation) : monomial a - 1 ∈ J := by
  have ha : a = (a 0) • translationBasis 0 + (a 1) • translationBasis 1 +
      (a 2) • translationBasis 2 := by
    funext i
    fin_cases i <;> simp [translationBasis]
  change a ∈ augmentationExponents
  rw [ha]
  exact augmentationExponents.add_mem
    (augmentationExponents.add_mem
      (augmentationExponents.zsmul_mem (basis_mem_augmentationExponents 0) (a 0))
      (augmentationExponents.zsmul_mem (basis_mem_augmentationExponents 1) (a 1)))
    (augmentationExponents.zsmul_mem (basis_mem_augmentationExponents 2) (a 2))

/-- Every Laurent polynomial is congruent to its value at `(1,1,1)` modulo `J`. -/
theorem sub_constant_augmentation_mem_J (f : R) :
    f - constant (augmentation f) ∈ J := by
  refine AddMonoidAlgebra.induction_on
    (motive := fun g : R => g - constant (augmentation g) ∈ J) f ?_ ?_ ?_
  · intro a
    change monomial a - constant (augmentation (monomial a)) ∈ J
    simpa only [augmentation_monomial, map_one] using monomial_sub_one_mem_J a
  · intro f g hf hg
    rw [map_add, map_add]
    convert J.add_mem hf hg using 1
    ring
  · intro c f hf
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · simp
    · simpa using hf

/-- The augmentation ideal is exactly `J = (x-1,y-1,z-1)`. -/
theorem ker_augmentation_eq_J : RingHom.ker augmentation = J := by
  apply le_antisymm ?_ J_le_ker_augmentation
  intro f hf
  have hfzero := RingHom.mem_ker.mp hf
  simpa [hfzero] using sub_constant_augmentation_mem_J f

/-- The concrete quotient identification `R/J ≅ 𝔽₂` from the manuscript. -/
def augmentationQuotientEquiv : R ⧸ J ≃+* ZMod 2 :=
  (Ideal.quotEquivOfEq ker_augmentation_eq_J.symm).trans
    (augmentation.quotientKerEquivOfSurjective augmentation_surjective)

@[simp] theorem augmentationQuotientEquiv_mk (f : R) :
    augmentationQuotientEquiv (Ideal.Quotient.mk J f) = augmentation f := by
  simp [augmentationQuotientEquiv]

end Decoupling
