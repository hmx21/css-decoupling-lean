import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.Ideal.Span
import Mathlib.RingTheory.Ideal.Maps

/-!
# Laurent-ring and adjoint conventions

This file formalizes the conventions in `notes/main.pdf`, Section 1:
`R = 𝔽₂[x±¹,y±¹,z±¹]`, conjugation reverses all translation exponents,
and `D† = (bar D)ᵀ`.  Exponents are functions `Fin 3 → ℤ`, in the
coordinate order `(x,y,z)`.  Thus this is the group algebra of `ℤ³`,
not a polynomial ring in three non-invertible variables.

Matrices act on column vectors; `Matrix m n R` represents a map `Rⁿ → Rᵐ`.
The definitions `u`, `v`, `w`, and `J` follow Section 1.3 verbatim.
-/

noncomputable section

namespace Decoupling

/-- The lattice of translation exponents, in the order `(x,y,z)`. -/
abbrev Translation := Fin 3 → ℤ

/-- The Laurent polynomial ring `𝔽₂[x±¹,y±¹,z±¹]`. -/
abbrev R := AddMonoidAlgebra (ZMod 2) Translation

/-- A Laurent monomial with coefficient one. -/
def monomial (a : Translation) : R := AddMonoidAlgebra.single a 1

@[simp] theorem monomial_zero : monomial 0 = 1 := rfl

@[simp] theorem monomial_mul (a b : Translation) :
    monomial a * monomial b = monomial (a + b) := by
  simp [monomial]

@[simp] theorem monomial_mul_neg (a : Translation) :
    monomial a * monomial (-a) = 1 := by simp

@[simp] theorem monomial_neg_mul (a : Translation) :
    monomial (-a) * monomial a = 1 := by simp

/-- The standard exponent in coordinate `i`. -/
def translationBasis (i : Fin 3) : Translation := Pi.single i 1

def x : R := monomial (translationBasis 0)
def y : R := monomial (translationBasis 1)
def z : R := monomial (translationBasis 2)

def u : R := x - 1
def v : R := y - 1
def w : R := z - 1

/-- The ideal `J = (u,v,w)` from Section 1.3. -/
def J : Ideal R := Ideal.span {u, v, w}

theorem u_mem_J : u ∈ J := Ideal.subset_span (by simp)
theorem v_mem_J : v ∈ J := Ideal.subset_span (by simp)
theorem w_mem_J : w ∈ J := Ideal.subset_span (by simp)

/-- Simultaneous inversion of the three translation directions. -/
def translationNeg : Translation ≃+ Translation where
  toFun := Neg.neg
  invFun := Neg.neg
  left_inv := neg_neg
  right_inv := neg_neg
  map_add' := neg_add

/-- Laurent conjugation fixes coefficients and reverses all exponents. -/
def bar : R ≃+* R :=
  AddMonoidAlgebra.mapDomainRingEquiv (ZMod 2) translationNeg

/-- The coefficient at exponent `a` after conjugation is the original coefficient at `-a`. -/
@[simp] theorem bar_coeff (f : R) (a : Translation) :
    (bar f).coeff a = f.coeff (-a) := by
  simp [bar, translationNeg, Finsupp.equivMapDomain_apply]

@[simp] theorem bar_monomial (a : Translation) :
    bar (monomial a) = monomial (-a) := by
  simp [bar, monomial, translationNeg]

@[simp] theorem bar_symm : bar.symm = bar := rfl

@[simp] theorem bar_bar (a : R) : bar (bar a) = a := by
  simpa only [bar_symm] using bar.symm_apply_apply a

@[simp] theorem bar_zero : bar (0 : R) = 0 := map_zero bar
@[simp] theorem bar_one : bar (1 : R) = 1 := map_one bar
@[simp] theorem bar_add (a b : R) : bar (a + b) = bar a + bar b := map_add bar a b
@[simp] theorem bar_mul (a b : R) : bar (a * b) = bar a * bar b := map_mul bar a b
@[simp] theorem bar_sub (a b : R) : bar (a - b) = bar a - bar b := map_sub bar a b

/-- Each monomial is a unit, and conjugation gives its multiplicative inverse. -/
@[simp] theorem monomial_mul_bar (a : Translation) :
    monomial a * bar (monomial a) = 1 := by simp

@[simp] theorem x_mul_bar_x : x * bar x = 1 := monomial_mul_bar _
@[simp] theorem y_mul_bar_y : y * bar y = 1 := monomial_mul_bar _
@[simp] theorem z_mul_bar_z : z * bar z = 1 := monomial_mul_bar _

@[simp] theorem laurent_neg_eq_self (a : R) : -a = a := by
  ext m
  simp

@[simp] theorem laurent_add_self (a : R) : a + a = 0 := by
  simpa only [laurent_neg_eq_self] using neg_add_cancel a

theorem laurent_sub_eq_add (a b : R) : a - b = a + b := by
  simp [sub_eq_add_neg]

/-- The concrete Laurent ring has the manuscript's characteristic two. -/
instance : CharP R 2 :=
  (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by
    simpa only [one_add_one_eq_two, Nat.cast_ofNat] using laurent_add_self (1 : R))

/-- Evaluation at `x = y = z = 1`, equivalently the sum of coefficients. -/
def augmentation : R →+* ZMod 2 :=
  AddMonoidAlgebra.liftNCRingHom (.id _) (1 : Multiplicative Translation →* ZMod 2)
    (by intro a b; exact Commute.one_right _)

@[simp] theorem augmentation_single (a : Translation) (c : ZMod 2) :
    augmentation (AddMonoidAlgebra.single a c) = c := by
  simp [augmentation]

@[simp] theorem augmentation_monomial (a : Translation) :
    augmentation (monomial a) = 1 := by
  simp [monomial]

@[simp] theorem augmentation_x : augmentation x = 1 := augmentation_monomial _
@[simp] theorem augmentation_y : augmentation y = 1 := augmentation_monomial _
@[simp] theorem augmentation_z : augmentation z = 1 := augmentation_monomial _
@[simp] theorem augmentation_u : augmentation u = 0 := by simp [u]
@[simp] theorem augmentation_v : augmentation v = 0 := by simp [v]
@[simp] theorem augmentation_w : augmentation w = 0 := by simp [w]

theorem augmentation_surjective : Function.Surjective augmentation := by
  intro c
  exact ⟨AddMonoidAlgebra.single 0 c, augmentation_single 0 c⟩

/-- The inclusion needed to descend augmentation through `R/J`.
This is only an inclusion; equality of the kernel with `J` is not asserted here. -/
theorem J_le_ker_augmentation : J ≤ RingHom.ker augmentation := by
  apply Ideal.span_le.mpr
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl | rfl <;> simp [RingHom.mem_ker]

/-- The adjoint `D† = (bar D)ᵀ`, including rectangular matrices. -/
def dagger {m n : Type*} (D : Matrix m n R) : Matrix n m R :=
  fun i j => bar (D j i)

scoped postfix:max "†" => dagger

@[simp] theorem dagger_apply {m n : Type*} (D : Matrix m n R) (i : n) (j : m) :
    dagger D i j = bar (D j i) := rfl

@[simp] theorem dagger_dagger {m n : Type*} (D : Matrix m n R) :
    dagger (dagger D) = D := by
  funext i j
  exact bar_bar _

@[simp] theorem dagger_zero {m n : Type*} :
    dagger (0 : Matrix m n R) = 0 := by
  funext i j
  exact bar_zero

@[simp] theorem dagger_add {m n : Type*} (A B : Matrix m n R) :
    dagger (A + B) = dagger A + dagger B := by
  funext i j
  exact bar_add _ _

@[simp] theorem dagger_sub {m n : Type*} (A B : Matrix m n R) :
    dagger (A - B) = dagger A - dagger B := by
  funext i j
  exact bar_sub _ _

@[simp] theorem dagger_one {m : Type*} [DecidableEq m] :
    dagger (1 : Matrix m m R) = 1 := by
  ext i j
  simp [dagger, Matrix.one_apply, eq_comm]

/-- Adjoint reverses composition in the manuscript's column-vector convention. -/
@[simp] theorem dagger_mul {m n k : Type*} [Fintype n]
    (A : Matrix m n R) (B : Matrix n k R) :
    dagger (A * B) = dagger B * dagger A := by
  ext i j
  simp [dagger, Matrix.mul_apply, map_sum, mul_comm]

end Decoupling
