import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.Algebra.MonoidAlgebra.Lift
import Mathlib.Data.Matrix.Mul
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Algebra.Field.ZMod

/-!
# Laurent coordinates in arbitrary dimension and characteristic

Source: `drafts/main.tex`, Section II.A, lines 158–181.
All definitions below use the actual group algebra of integer translations.
No characteristic-two identities are imported or assumed. Dimension zero is
allowed in this algebraic foundation; the final code theorem assumes D ≥ 2.
-/

noncomputable section

namespace Decoupling.HighDim

abbrev Translation (D : ℕ) := Fin D → ℤ
abbrev Laurent (K : Type*) [CommRing K] (D : ℕ) :=
  AddMonoidAlgebra K (Translation D)

variable {K : Type*} [CommRing K] {D : ℕ}

def monomial (K : Type*) [CommRing K] {D : ℕ} (a : Translation D) : Laurent K D :=
  AddMonoidAlgebra.single a 1

@[simp] theorem monomial_zero : monomial K (0 : Translation D) = 1 := rfl

@[simp] theorem monomial_mul (a b : Translation D) :
    monomial K a * monomial K b = monomial K (a + b) := by
  simp [monomial]

@[simp] theorem monomial_mul_neg (a : Translation D) :
    monomial K a * monomial K (-a) = 1 := by simp

@[simp] theorem monomial_neg_mul (a : Translation D) :
    monomial K (-a) * monomial K a = 1 := by simp

def translationBasis (i : Fin D) : Translation D := Pi.single i 1
def coordinate (K : Type*) [CommRing K] {D : ℕ} (i : Fin D) : Laurent K D :=
  monomial K (translationBasis i)
def difference (K : Type*) [CommRing K] {D : ℕ} (i : Fin D) : Laurent K D :=
  coordinate K i - 1
def augmentationIdeal (K : Type*) [CommRing K] (D : ℕ) : Ideal (Laurent K D) :=
  Ideal.span (Set.range (difference K : Fin D → Laurent K D))

theorem difference_mem_augmentationIdeal (i : Fin D) :
    difference K i ∈ augmentationIdeal K D :=
  Ideal.subset_span (Set.mem_range_self i)

def translationNeg (D : ℕ) : Translation D ≃+ Translation D where
  toFun := Neg.neg
  invFun := Neg.neg
  left_inv := neg_neg
  right_inv := neg_neg
  map_add' := neg_add

def bar : Laurent K D ≃+* Laurent K D :=
  AddMonoidAlgebra.mapDomainRingEquiv K (translationNeg D)

@[simp] theorem bar_coeff (f : Laurent K D) (a : Translation D) :
    (bar f).coeff a = f.coeff (-a) := by
  simp [bar, translationNeg, Finsupp.equivMapDomain_apply]

@[simp] theorem bar_monomial (a : Translation D) :
    bar (monomial K a) = monomial K (-a) := by
  simp [bar, monomial, translationNeg]

@[simp] theorem bar_symm : (bar : Laurent K D ≃+* Laurent K D).symm = bar := rfl

@[simp] theorem bar_bar (f : Laurent K D) : bar (bar f) = f := by
  simpa only [bar_symm] using (bar : Laurent K D ≃+* Laurent K D).symm_apply_apply f

@[simp] theorem bar_zero : bar (0 : Laurent K D) = 0 := map_zero bar
@[simp] theorem bar_one : bar (1 : Laurent K D) = 1 := map_one bar
@[simp] theorem bar_add (a b : Laurent K D) : bar (a + b) = bar a + bar b := map_add bar a b
@[simp] theorem bar_mul (a b : Laurent K D) : bar (a * b) = bar a * bar b := map_mul bar a b
@[simp] theorem bar_sub (a b : Laurent K D) : bar (a - b) = bar a - bar b := map_sub bar a b
@[simp] theorem bar_neg (a : Laurent K D) : bar (-a) = -bar a := map_neg bar a

def constant : K →+* Laurent K D := AddMonoidAlgebra.singleZeroRingHom

@[simp] theorem constant_apply (c : K) :
    (constant c : Laurent K D) = AddMonoidAlgebra.single 0 c := rfl

def augmentation : Laurent K D →+* K :=
  AddMonoidAlgebra.liftNCRingHom (.id _) (1 : Multiplicative (Translation D) →* K)
    (by intro a b; exact Commute.one_right _)

@[simp] theorem augmentation_single (a : Translation D) (c : K) :
    augmentation (AddMonoidAlgebra.single a c) = c := by
  simp [augmentation]

@[simp] theorem augmentation_monomial (a : Translation D) :
    augmentation (monomial K a) = 1 := by simp [monomial]

@[simp] theorem augmentation_constant (c : K) :
    augmentation (constant c : Laurent K D) = c := by simp

@[simp] theorem augmentation_coordinate (i : Fin D) :
    augmentation (coordinate K i) = 1 := augmentation_monomial _

@[simp] theorem augmentation_difference (i : Fin D) :
    augmentation (difference K i) = 0 := by simp [difference]

theorem augmentation_surjective : Function.Surjective (augmentation : Laurent K D →+* K) := by
  intro c
  exact ⟨constant c, augmentation_constant c⟩

theorem augmentationIdeal_le_ker : augmentationIdeal K D ≤ RingHom.ker augmentation := by
  apply Ideal.span_le.mpr
  rintro _ ⟨i, rfl⟩
  simp [RingHom.mem_ker]

def dagger {m n : Type*} (A : Matrix m n (Laurent K D)) : Matrix n m (Laurent K D) :=
  fun i j => bar (A j i)

@[simp] theorem dagger_apply {m n : Type*} (A : Matrix m n (Laurent K D)) (i : n) (j : m) :
    dagger A i j = bar (A j i) := rfl

@[simp] theorem dagger_dagger {m n : Type*} (A : Matrix m n (Laurent K D)) :
    dagger (dagger A) = A := by
  funext i j
  exact bar_bar _

@[simp] theorem dagger_zero {m n : Type*} :
    dagger (0 : Matrix m n (Laurent K D)) = 0 := by
  funext i j
  exact bar_zero

@[simp] theorem dagger_add {m n : Type*} (A B : Matrix m n (Laurent K D)) :
    dagger (A + B) = dagger A + dagger B := by
  funext i j
  exact bar_add _ _

@[simp] theorem dagger_sub {m n : Type*} (A B : Matrix m n (Laurent K D)) :
    dagger (A - B) = dagger A - dagger B := by
  funext i j
  exact bar_sub _ _

@[simp] theorem dagger_neg {m n : Type*} (A : Matrix m n (Laurent K D)) :
    dagger (-A) = -dagger A := by
  funext i j
  exact bar_neg _

@[simp] theorem dagger_one {m : Type*} [DecidableEq m] :
    dagger (1 : Matrix m m (Laurent K D)) = 1 := by
  ext i j
  simp [dagger, Matrix.one_apply, eq_comm]

@[simp] theorem dagger_mul {m n k : Type*} [Fintype n]
    (A : Matrix m n (Laurent K D)) (B : Matrix n k (Laurent K D)) :
    dagger (A * B) = dagger B * dagger A := by
  ext i j
  simp [dagger, Matrix.mul_apply, map_sum, mul_comm]

end Decoupling.HighDim
