import Decoupling.Augmentation

/-!
# Partial evaluation of the Laurent variables

`evalX` sets `x = 1` and retains `y,z`; `evalXY` sets `x = y = 1`
and retains `z`.  They are endomorphisms of the concrete Laurent ring,
so all variable names retain the conventions of `notes/main.pdf`.
Their kernels are proved to be `(u)` and `(u,v)`, respectively.
These kernel computations support the regular-sequence claims for the
Koszul complex; no regularity hypothesis is used here.
-/

noncomputable section

namespace Decoupling.PartialEvaluation

/-- Erase the `x` exponent and retain the `y,z` exponents. -/
def dropX : Translation →+ Translation where
  toFun a i := if i = 0 then 0 else a i
  map_zero' := by funext i; simp
  map_add' := by intro a b; funext i; by_cases hi : i = 0 <;> simp [hi]

/-- Retain only the `z` exponent. -/
def dropXY : Translation →+ Translation where
  toFun a i := if i = 2 then a i else 0
  map_zero' := by funext i; simp
  map_add' := by intro a b; funext i; by_cases hi : i = 2 <;> simp [hi]

@[simp] theorem dropX_basis_zero : dropX (translationBasis 0) = 0 := by
  funext i
  fin_cases i <;> simp [dropX, translationBasis]

@[simp] theorem dropX_basis_one : dropX (translationBasis 1) = translationBasis 1 := by
  funext i
  fin_cases i <;> simp [dropX, translationBasis]

@[simp] theorem dropX_basis_two : dropX (translationBasis 2) = translationBasis 2 := by
  funext i
  fin_cases i <;> simp [dropX, translationBasis]

@[simp] theorem dropXY_basis_zero : dropXY (translationBasis 0) = 0 := by
  funext i
  fin_cases i <;> simp [dropXY, translationBasis]

@[simp] theorem dropXY_basis_one : dropXY (translationBasis 1) = 0 := by
  funext i
  fin_cases i <;> simp [dropXY, translationBasis]

@[simp] theorem dropXY_basis_two : dropXY (translationBasis 2) = translationBasis 2 := by
  funext i
  fin_cases i <;> simp [dropXY, translationBasis]

/-- The ring map induced by an additive map of translation exponents. -/
def partialMap (p : Translation →+ Translation) : R →+* R :=
  AddMonoidAlgebra.mapDomainRingHom (ZMod 2) p

@[simp] theorem partialMap_monomial (p : Translation →+ Translation) (a : Translation) :
    partialMap p (monomial a) = monomial (p a) := by
  simp [partialMap, monomial]

/-- Evaluation at `x = 1`. -/
def evalX : R →+* R := partialMap dropX

/-- Evaluation at `x = y = 1`. -/
def evalXY : R →+* R := partialMap dropXY

@[simp] theorem evalX_x : evalX x = 1 := by simp [evalX, x]
@[simp] theorem evalX_y : evalX y = y := by simp [evalX, y]
@[simp] theorem evalX_z : evalX z = z := by simp [evalX, z]
@[simp] theorem evalXY_x : evalXY x = 1 := by simp [evalXY, x]
@[simp] theorem evalXY_y : evalXY y = 1 := by simp [evalXY, y]
@[simp] theorem evalXY_z : evalXY z = z := by simp [evalXY, z]

@[simp] theorem evalX_u : evalX u = 0 := by simp [u]
@[simp] theorem evalX_v : evalX v = v := by simp [v]
@[simp] theorem evalX_w : evalX w = w := by simp [w]
@[simp] theorem evalXY_u : evalXY u = 0 := by simp [u]
@[simp] theorem evalXY_v : evalXY v = 0 := by simp [v]
@[simp] theorem evalXY_w : evalXY w = w := by simp [w]

/-- A monomial agrees modulo `I` with its image under a map of exponents. -/
theorem monomial_sub_partialMap_mem (I : Ideal R) (p : Translation →+ Translation)
    (h : ∀ a, a - p a ∈ monomialCongruenceExponents I) (a : Translation) :
    monomial a - partialMap p (monomial a) ∈ I := by
  rw [partialMap_monomial]
  have hmul : monomial (p a) * monomial (a - p a) = monomial a := by
    rw [monomial_mul]
    congr 1
    abel
  simpa only [mul_sub, hmul, mul_one] using I.mul_mem_left (monomial (p a)) (h a)

/-- Extension of monomial congruences to all Laurent polynomials. -/
theorem sub_partialMap_mem (I : Ideal R) (p : Translation →+ Translation)
    (h : ∀ a, a - p a ∈ monomialCongruenceExponents I) (f : R) :
    f - partialMap p f ∈ I := by
  refine AddMonoidAlgebra.induction_on
    (motive := fun g : R => g - partialMap p g ∈ I) f ?_ ?_ ?_
  · intro a
    change monomial a - partialMap p (monomial a) ∈ I
    exact monomial_sub_partialMap_mem I p h a
  · intro f g hf hg
    rw [map_add]
    convert I.add_mem hf hg using 1
    ring
  · intro c f hf
    have hc : c = 0 ∨ c = 1 := by
      fin_cases c
      · exact Or.inl rfl
      · exact Or.inr rfl
    rcases hc with rfl | rfl
    · simp
    · simpa using hf

private theorem dropX_difference_mem (a : Translation) :
    a - dropX a ∈ monomialCongruenceExponents (Ideal.span {u}) := by
  have ha : a - dropX a = (a 0) • translationBasis 0 := by
    funext i
    fin_cases i <;> simp [dropX, translationBasis]
  rw [ha]
  apply (monomialCongruenceExponents (Ideal.span {u})).zsmul_mem
  exact Ideal.subset_span (by simp [u, x])

private theorem dropXY_difference_mem (a : Translation) :
    a - dropXY a ∈ monomialCongruenceExponents (Ideal.span {u, v}) := by
  have ha : a - dropXY a = (a 0) • translationBasis 0 + (a 1) • translationBasis 1 := by
    funext i
    fin_cases i <;> simp [dropXY, translationBasis]
  rw [ha]
  apply (monomialCongruenceExponents (Ideal.span {u, v})).add_mem
  · apply (monomialCongruenceExponents (Ideal.span {u, v})).zsmul_mem
    exact Ideal.subset_span (by simp [u, x])
  · apply (monomialCongruenceExponents (Ideal.span {u, v})).zsmul_mem
    exact Ideal.subset_span (by simp [v, y])

theorem sub_evalX_mem (f : R) : f - evalX f ∈ Ideal.span {u} :=
  sub_partialMap_mem (Ideal.span {u}) dropX dropX_difference_mem f

theorem sub_evalXY_mem (f : R) : f - evalXY f ∈ Ideal.span {u, v} :=
  sub_partialMap_mem (Ideal.span {u, v}) dropXY dropXY_difference_mem f

/-- The kernel of evaluation at `x = 1` is `(x-1) = (u)`. -/
theorem ker_evalX : RingHom.ker evalX = Ideal.span {u} := by
  apply le_antisymm
  · intro f hf
    have hfzero := RingHom.mem_ker.mp hf
    simpa [hfzero] using sub_evalX_mem f
  · apply Ideal.span_le.mpr
    intro f hf
    simp only [Set.mem_singleton_iff] at hf
    subst f
    simp [RingHom.mem_ker]

/-- The kernel of evaluation at `x = y = 1` is `(x-1,y-1) = (u,v)`. -/
theorem ker_evalXY : RingHom.ker evalXY = Ideal.span {u, v} := by
  apply le_antisymm
  · intro f hf
    have hfzero := RingHom.mem_ker.mp hf
    simpa [hfzero] using sub_evalXY_mem f
  · apply Ideal.span_le.mpr
    intro f hf
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
    rcases hf with rfl | rfl <;> simp [RingHom.mem_ker]

end Decoupling.PartialEvaluation
