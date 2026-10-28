import Decoupling.GeneralRetained
import Decoupling.FrobeniusDuality
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Coefficient extraction and dual restriction for the actual retained ring

For every positive period `n`, the retained subring is the literal
`S n = 𝔽₂[x±ⁿ,y±ⁿ,z±ⁿ] ⊆ R`.  Its extraction map retains precisely
those Laurent coefficients.  The residue monomials and their inverses
are dual under this extraction pairing.
-/

noncomputable section

namespace Decoupling.RestrictionDuality

open GeneralRetained Matrix Module

variable (n : ℕ) [NeZero n]

@[simp] theorem residueExponent_zero : residueExponent n (0 : Residue n) = 0 := by
  funext i
  change ((0 : Fin n) : ℤ) = 0
  simp

/-- Retain only the monomials whose exponents belong to the retained lattice. -/
def τ : R →ₗ[S n] S n := (residueBasis n).coord 0

/-- Coefficientwise meaning of extraction, with the retained variables renamed. -/
theorem τ_coeff (r : R) (a : Translation) :
    ((renameEquiv n).symm (τ n r)).coeff a = r.coeff (scaleExponent n a) := by
  simp [τ, Basis.coord_apply, residueBasis_repr, decomposeAddEquiv,
    Finsupp.domCongr, exponentEquiv_symm]

@[simp] theorem τ_one : τ n 1 = 1 := by
  have hzero : residueBasis n (0 : Residue n) = 1 := by
    simp
  rw [← hzero]
  simp only [τ, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]

@[simp] theorem τ_algebraMap (s : S n) : τ n (algebraMap (S n) R s) = s := by
  change τ n (s : R) = s
  have h : τ n ((s : R) * 1) = s * τ n 1 := (τ n).map_smul s (1 : R)
  simpa only [mul_one, τ_one] using h

/-- Conjugation on the retained ring, with the same Laurent convention. -/
def barS : S n ≃+* S n :=
  (renameEquiv n).symm.trans (bar.trans (renameEquiv n))

@[simp] theorem barS_barS (s : S n) : barS n (barS n s) = s := by
  simp [barS]

@[simp] theorem barS_rename (r : R) : barS n (renameEquiv n r) = renameEquiv n (bar r) := by
  simp [barS]

omit [NeZero n] in
theorem embed_bar (r : R) : embed n (bar r) = bar (embed n r) := by
  have h : (embed n).toAddMonoidHom.comp bar.toAddMonoidHom =
      bar.toAddMonoidHom.comp (embed n).toAddMonoidHom := by
    apply AddMonoidAlgebra.addMonoidHom_ext
    intro a c
    simp [embed, bar, translationNeg]
  exact DFunLike.congr_fun h r

/-- Retained conjugation is the restriction of the original Laurent conjugation. -/
@[simp] theorem coe_barS (s : S n) : (barS n s : R) = bar (s : R) := by
  obtain ⟨r, rfl⟩ := (renameEquiv n).surjective s
  rw [barS_rename]
  exact embed_bar n r

/-- Extraction commutes with Laurent conjugation. -/
theorem τ_bar (r : R) : τ n (bar r) = barS n (τ n r) := by
  apply (renameEquiv n).symm.injective
  ext a
  rw [τ_coeff]
  simp only [barS, RingEquiv.trans_apply, RingEquiv.symm_apply_apply, bar_coeff]
  rw [τ_coeff]
  congr 1
  funext i
  simp [scaleExponent]

private theorem residue_eq_of_scaled_difference (p q : Residue n) (a : Translation)
    (h : scaleExponent n a = residueExponent n q - residueExponent n p) : p = q := by
  have he : (exponentEquiv n).symm (p, a) = (exponentEquiv n).symm (q, 0) := by
    rw [exponentEquiv_symm, exponentEquiv_symm, map_zero, zero_add, h]
    abel
  exact congrArg Prod.fst ((exponentEquiv n).symm.injective he)

/-- The residue monomials and their Laurent inverses are dual for extraction. -/
theorem τ_inverse_basis (p q : Residue n) :
    τ n (bar (residueBasis n p) * residueBasis n q) = if p = q then 1 else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    simp
  · simp only [hpq, ↓reduceIte]
    rw [residueBasis_apply, residueBasis_apply, bar_monomial, monomial_mul]
    apply (renameEquiv n).symm.injective
    ext a
    rw [τ_coeff]
    have hne : -residueExponent n p + residueExponent n q ≠ scaleExponent n a := by
      intro ha
      apply hpq
      apply residue_eq_of_scaled_difference n p q a
      rw [← ha]
      abel
    simp [monomial, hne]

theorem τ_basis_inverse (p q : Residue n) :
    τ n (residueBasis n p * bar (residueBasis n q)) = if p = q then 1 else 0 := by
  simpa only [mul_comm, eq_comm] using τ_inverse_basis n q p

/-- Pairing with an inverse monomial extracts exactly the corresponding basis coordinate. -/
theorem τ_inverse_mul_eq_coord (p : Residue n) (r : R) :
    τ n (bar (residueBasis n p) * r) = (residueBasis n).coord p r := by
  have h : (τ n).comp (LinearMap.mul (S n) R (bar (residueBasis n p))) =
      (residueBasis n).coord p := by
    apply (residueBasis n).ext
    intro q
    change τ n (bar (residueBasis n p) * residueBasis n q) = (residueBasis n).coord p _
    rw [τ_inverse_basis]
    simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, eq_comm]
  exact DFunLike.congr_fun h r

/-- The `S`-bilinear coefficient-extraction pairing. -/
def pairingMap : R →ₗ[S n] (R →ₗ[S n] S n) where
  toFun r := {
    toFun a := τ n (a * r)
    map_add' a b := by simp [add_mul]
    map_smul' s a := by simp
  }
  map_add' r s := by
    apply LinearMap.ext
    intro a
    change τ n (a * (r + s)) = τ n (a * r) + τ n (a * s)
    simp [mul_add]
  map_smul' s r := by
    apply LinearMap.ext
    intro a
    change τ n (a * (s • r)) = s • τ n (a * r)
    simp

@[simp] theorem pairingMap_apply (r a : R) : pairingMap n r a = τ n (a * r) := rfl

theorem pairingMap_injective : Function.Injective (pairingMap n) := by
  intro r s hrs
  apply (residueBasis n).repr.injective
  apply Finsupp.ext
  intro p
  change (residueBasis n).coord p r = (residueBasis n).coord p s
  rw [← τ_inverse_mul_eq_coord, ← τ_inverse_mul_eq_coord]
  exact DFunLike.congr_fun hrs (bar (residueBasis n p))

theorem pairingMap_surjective : Function.Surjective (pairingMap n) := by
  classical
  intro g
  refine ⟨∑ p, g (residueBasis n p) • bar (residueBasis n p), ?_⟩
  apply (residueBasis n).ext
  intro q
  change τ n (residueBasis n q * ∑ p, g (residueBasis n p) • bar (residueBasis n p)) = _
  rw [Finset.mul_sum, map_sum]
  simp only [mul_smul_comm, map_smul, τ_basis_inverse, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  simp

/-- Perfectness proved for the actual retained ring, at every positive period. -/
def pairingEquiv : R ≃ₗ[S n] (R →ₗ[S n] S n) :=
  LinearEquiv.ofBijective (pairingMap n) ⟨pairingMap_injective n, pairingMap_surjective n⟩

/-- The concrete perfect-pairing data used in the general dual-restriction construction. -/
def frobeniusPairing : FrobeniusDuality.Pairing (S n) R where
  trace := τ n
  dualEquiv := pairingEquiv n
  dual_apply _ _ := rfl

/-- The actual multiplication matrix in the retained residue basis. -/
def expandScalar : R →ₐ[S n] Matrix (Residue n) (Residue n) (S n) :=
  Algebra.leftMulMatrix (residueBasis n)

/-- The manuscript's entry formula for the physical multiplication matrix. -/
theorem expandScalar_apply (r : R) (p q : Residue n) :
    expandScalar n r p q = τ n (bar (residueBasis n p) * r * residueBasis n q) := by
  rw [expandScalar, Algebra.leftMulMatrix_eq_repr_mul]
  change (residueBasis n).coord p (r * residueBasis n q) = _
  rw [← τ_inverse_mul_eq_coord, mul_assoc]

/-- Dagger over the actual retained coefficient ring. -/
def daggerS {m k : Type*} (D : Matrix m k (S n)) : Matrix k m (S n) :=
  fun i j => barS n (D j i)

/-- Conjugating a Laurent scalar gives the adjoint of its multiplication matrix. -/
theorem expandScalar_bar (r : R) : expandScalar n (bar r) = daggerS n (expandScalar n r) := by
  funext p q
  change expandScalar n (bar r) p q = barS n (expandScalar n r q p)
  rw [expandScalar_apply, expandScalar_apply, ← τ_bar]
  congr 1
  simp only [bar_mul, bar_bar]
  ring

/-- Physical coarse-graining expands every Laurent entry into its multiplication matrix. -/
def expandMatrix {m k : Type*} (D : Matrix m k R) :
    Matrix (m × Residue n) (k × Residue n) (S n) :=
  fun i j => expandScalar n (D i.1 j.1) i.2 j.2

@[simp] theorem expandMatrix_zero {m k : Type*} :
    expandMatrix n (0 : Matrix m k R) = 0 := by
  funext i j
  simp [expandMatrix]

@[simp] theorem expandMatrix_one {m : Type*} [DecidableEq m] :
    expandMatrix n (1 : Matrix m m R) = 1 := by
  classical
  funext i j
  rcases i with ⟨i, p⟩
  rcases j with ⟨j, q⟩
  by_cases hij : i = j
  · subst j
    simp [expandMatrix, Matrix.one_apply]
  · simp [expandMatrix, hij]

/-- Dagger commutes with the actual physical matrix expansion, including rectangular matrices. -/
theorem expandMatrix_dagger {m k : Type*} (D : Matrix m k R) :
    expandMatrix n (dagger D) = daggerS n (expandMatrix n D) := by
  funext i j
  exact congrFun₂ (expandScalar_bar n (D j.1 i.1)) i.2 j.2

theorem expandMatrix_mul {m k l : Type*} [Fintype k]
    (D : Matrix m k R) (E : Matrix k l R) :
    expandMatrix n (D * E) = expandMatrix n D * expandMatrix n E := by
  funext i j
  simp [expandMatrix, Matrix.mul_apply, map_sum, Fintype.sum_prod_type, Matrix.sum_apply]

/-- Coordinates of a physical vector after retaining the coarser lattice. -/
def expandVector {m : Type*} (v : m → R) : (m × Residue n) → S n :=
  fun i => (residueBasis n).coord i.2 (v i.1)

/-- The residue-coordinate change for physical vectors is an actual linear equivalence. -/
def vectorEquiv (m : Type*) : (m → R) ≃ₗ[S n] ((m × Residue n) → S n) where
  toFun := expandVector n
  invFun v i := (residueBasis n).equivFun.symm (fun p => v (i, p))
  map_add' v w := by funext i; simp [expandVector]
  map_smul' s v := by funext i; simp [expandVector]
  left_inv v := by
    funext i
    exact (residueBasis n).equivFun.symm_apply_apply (v i)
  right_inv v := by
    funext i
    exact congrFun ((residueBasis n).equivFun.apply_symm_apply (fun p => v (i.1, p))) i.2

@[simp] theorem vectorEquiv_apply {m : Type*} (v : m → R) :
    vectorEquiv n m v = expandVector n v := rfl

/-- The expanded check matrix acts on the unchanged physical vector in residue coordinates. -/
theorem expandMatrix_mulVec {m k : Type*} [Fintype k]
    (D : Matrix m k R) (v : k → R) :
    expandMatrix n D *ᵥ expandVector n v = expandVector n (D *ᵥ v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, expandMatrix, expandVector]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrFun (Algebra.leftMulMatrix_mulVec_repr (residueBasis n) (D i.1 j) (v j)) i.2

@[simp] theorem expandVector_eq_zero_iff {m : Type*} (v : m → R) :
    expandVector n v = 0 ↔ v = 0 := (vectorEquiv n m).map_eq_zero_iff

theorem expanded_kernel_iff {m k : Type*} [Fintype k]
    (D : Matrix m k R) (v : k → R) :
    expandMatrix n D *ᵥ expandVector n v = 0 ↔ D *ᵥ v = 0 := by
  rw [expandMatrix_mulVec, expandVector_eq_zero_iff]

theorem expanded_image_iff {k l : Type*} [Fintype l]
    (E : Matrix k l R) (v : k → R) :
    (∃ z, E *ᵥ z = v) ↔ ∃ z, expandMatrix n E *ᵥ z = expandVector n v := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨expandVector n z, by rw [expandMatrix_mulVec, hz]⟩
  · rintro ⟨z, hz⟩
    obtain ⟨z, rfl⟩ := (vectorEquiv n l).surjective z
    refine ⟨z, (vectorEquiv n k).injective ?_⟩
    simpa only [vectorEquiv_apply, expandMatrix_mulVec] using hz

/-- Actual physical expansion preserves exactness, hence each topological equality. -/
theorem exactness_preserved {m k l : Type*} [Fintype k] [Fintype l]
    (D : Matrix m k R) (E : Matrix k l R)
    (hexact : ∀ v, D *ᵥ v = 0 ↔ ∃ z, E *ᵥ z = v) :
    ∀ v, expandMatrix n D *ᵥ v = 0 ↔ ∃ z, expandMatrix n E *ᵥ z = v := by
  intro v
  obtain ⟨v, rfl⟩ := (vectorEquiv n k).surjective v
  rw [vectorEquiv_apply, expanded_kernel_iff, ← expanded_image_iff]
  exact hexact v

variable {V : Type*} [AddCommGroup V] [Module R V] [Module (S n) V]
  [IsScalarTower (S n) R V]

/-- The manuscript's dual restriction, now for the actual retained subring. -/
def dualRestrictEquiv : (V →ₗ[R] R) ≃ₗ[S n] (V →ₗ[S n] S n) :=
  (frobeniusPairing n).dualRestrictEquiv

@[simp] theorem dualRestrictEquiv_apply (f : V →ₗ[R] R) (v : V) :
    dualRestrictEquiv n f v = τ n (f v) := rfl

variable {W : Type*} [AddCommGroup W] [Module R W] [Module (S n) W]
  [IsScalarTower (S n) R W]

/-- Naturality for the unchanged original map under restriction of scalars. -/
theorem dualRestrict_naturality (f : V →ₗ[R] W) (g : W →ₗ[R] R) :
    dualRestrictEquiv n (g.comp f) =
      (dualRestrictEquiv n g).comp (f.restrictScalars (S n)) := rfl

end Decoupling.RestrictionDuality
