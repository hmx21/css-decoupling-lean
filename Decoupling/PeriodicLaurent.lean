import Decoupling.RestrictionDuality
import Mathlib.Data.ZMod.Basic

/-!
# Actual Laurent matrices on a finite periodic three-dimensional lattice

The finite cell set is `(Fin L)^3`, canonically equivalent to `(ZMod L)^3`.
`L>0` is represented by `NeZero L`. Scalar entries are the actual retained
multiplication matrices followed by evaluation of the retained translations
at one, so all integer displacements, including negative ones, wrap modulo L.
-/

namespace Decoupling.PeriodicLaurent

open GeneralRetained RestrictionDuality Matrix

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (L : ℕ) [NeZero L]

abbrev Cell := Residue L

def cellEquiv : Cell L ≃ (Fin 3 → ZMod L) :=
  Equiv.piCongrRight fun _ => (ZMod.finEquiv L).toEquiv

/-- Integer translation reduced in every coordinate modulo the actual period. -/
def periodMap : Translation →+ Cell L where
  toFun a i := (ZMod.finEquiv L).symm (a i : ZMod L)
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp

/-- The finite-coordinate model is literally reduction modulo L in `(ZMod L)^3`. -/
theorem cellEquiv_periodMap (a : Translation) :
    cellEquiv L (periodMap L a) = fun i => (a i : ZMod L) := by
  funext i
  exact (ZMod.finEquiv L).apply_symm_apply _

omit [NeZero L] in
theorem cell_card : Fintype.card (Cell L) = L ^ 3 := by
  simp [Cell, Residue]

@[simp] theorem periodMap_residue (p : Cell L) : periodMap L (residueExponent L p) = p := by
  funext i
  apply (ZMod.finEquiv L).injective
  cases L with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ n =>
    change (((p i).val : ℤ) : ZMod (n + 1)) = (show ZMod (n + 1) from p i)
    rw [Int.cast_natCast]
    exact ZMod.natCast_zmod_val (show ZMod (n + 1) from p i)

@[simp] theorem periodMap_scale (a : Translation) : periodMap L (scaleExponent L a) = 0 := by
  funext i
  simp [periodMap, scaleExponent]

theorem exponentEquiv_fst (a : Translation) : (exponentEquiv L a).1 = periodMap L a := by
  have h := congrArg (periodMap L) ((exponentEquiv L).symm_apply_apply a)
  rw [exponentEquiv_symm, map_add, periodMap_scale, periodMap_residue, zero_add] at h
  exact h

/-- The retained translation variables are evaluated at one. -/
def coefficient : S L →+* ZMod 2 := augmentation.comp (retained L).subtype

@[simp] theorem coefficient_rename (r : R) : coefficient L (renameEquiv L r) = augmentation r := by
  change augmentation (embed L r) = augmentation r
  have h : augmentation.comp (embed L) = augmentation := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro c
      simp [embed, augmentation]
    · intro a
      simp [embed]
  exact DFunLike.congr_fun h r

@[simp] theorem coefficient_bar (r : S L) : coefficient L (barS L r) = coefficient L r := by
  obtain ⟨q, rfl⟩ := (renameEquiv L).surjective r
  rw [barS_rename, coefficient_rename, coefficient_rename]
  have h : augmentation.comp bar.toRingHom = augmentation := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro c
      simp [bar, translationNeg, augmentation]
    · intro a
      simp [bar, translationNeg, augmentation]
  exact DFunLike.congr_fun h q

/-- The actual finite translation representation of one Laurent scalar. -/
def scalar : R →+* Matrix (Cell L) (Cell L) (ZMod 2) :=
  (coefficient L).mapMatrix.comp (expandScalar L).toRingHom

/-- A monomial translates a cell by its integer displacement modulo L. -/
theorem scalar_monomial (a : Translation) (p q : Cell L) :
    scalar L (monomial a) p q = if p = q + periodMap L a then 1 else 0 := by
  change coefficient L (expandScalar L (monomial a) p q) = _
  rw [expandScalar, Algebra.leftMulMatrix_eq_repr_mul, residueBasis_apply, monomial_mul,
    residueBasis_repr]
  change coefficient L (decomposeAddEquiv L (AddMonoidAlgebra.single
    (a + residueExponent L q) 1) p) = _
  rw [decompose_single, Finsupp.single_apply]
  simp only [exponentEquiv_fst, map_add, periodMap_residue]
  split_ifs <;> simp_all [add_comm, eq_comm]

/-- Laurent conjugation becomes the ordinary finite binary transpose. -/
theorem scalar_bar (r : R) : scalar L (bar r) = (scalar L r)ᵀ := by
  ext p q
  change coefficient L (expandScalar L (bar r) p q) = _
  rw [expandScalar_bar]
  exact coefficient_bar L _

/-- Every Laurent entry acts between the corresponding species/cell indices. -/
def matrix {m k : Type*} (D : Matrix m k R) :
    Matrix (m × Cell L) (k × Cell L) (ZMod 2) :=
  (expandMatrix L D).map (coefficient L)

@[simp] theorem matrix_apply {m k : Type*} (D : Matrix m k R) (i : m × Cell L) (j : k × Cell L) :
    matrix L D i j = scalar L (D i.1 j.1) i.2 j.2 := rfl

@[simp] theorem matrix_zero {m k : Type*} : matrix L (0 : Matrix m k R) = 0 := by
  ext i j
  simp

@[simp] theorem matrix_one {m : Type*} [DecidableEq m] :
    matrix L (1 : Matrix m m R) = 1 := by
  rw [matrix, expandMatrix_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem matrix_add {m k : Type*} (D E : Matrix m k R) :
    matrix L (D + E) = matrix L D + matrix L E := by
  ext i j
  simp

theorem matrix_mul {m k t : Type*} [Fintype k] (D : Matrix m k R) (E : Matrix k t R) :
    matrix L (D * E) = matrix L D * matrix L E := by
  rw [matrix, expandMatrix_mul, Matrix.map_mul]
  rfl

theorem matrix_dagger {m k : Type*} (D : Matrix m k R) :
    matrix L (dagger D) = (matrix L D)ᵀ := by
  ext i j
  exact congrFun₂ (scalar_bar L (D j.1 i.1)) i.2 j.2


/-- Actual containment of Laurent column images gives a matrix factor.
This is the finite free-domain lifting argument, with no flatness premise. -/
theorem factor_of_image {m k t : Type*} [Fintype k] [Fintype t] [DecidableEq k]
    (D : Matrix m k R) (E : Matrix m t R)
    (h : ∀ v, (∃ x, D *ᵥ x = v) → ∃ y, E *ᵥ y = v) :
    ∃ F : Matrix t k R, E * F = D := by
  choose f hf using fun j : k => h (D *ᵥ Pi.single j 1) ⟨Pi.single j 1, rfl⟩
  refine ⟨fun i j => f j i, ?_⟩
  funext i j
  have hi := congrFun (hf j) i
  rw [Matrix.mulVec_single_one] at hi
  simpa only [Matrix.col_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct] using hi

/-- Periodic specialization preserves equality of generator images, even
though the periodic quotient is not asserted to be flat. -/
theorem image_iff {m k t : Type*} [Fintype k] [Fintype t] [DecidableEq k] [DecidableEq t]
    (D : Matrix m k R) (E : Matrix m t R)
    (h : ∀ v, (∃ x, D *ᵥ x = v) ↔ ∃ y, E *ᵥ y = v)
    (v : m × Cell L → ZMod 2) :
    (∃ x, matrix L D *ᵥ x = v) ↔ ∃ y, matrix L E *ᵥ y = v := by
  obtain ⟨F, hF⟩ := factor_of_image D E (fun v => (h v).mp)
  obtain ⟨G, hG⟩ := factor_of_image E D (fun v => (h v).mpr)
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨matrix L F *ᵥ x, ?_⟩
    rw [Matrix.mulVec_mulVec, ← matrix_mul, hF]
  · rintro ⟨y, rfl⟩
    refine ⟨matrix L G *ᵥ y, ?_⟩
    rw [Matrix.mulVec_mulVec, ← matrix_mul, hG]

end
end Decoupling.PeriodicLaurent
