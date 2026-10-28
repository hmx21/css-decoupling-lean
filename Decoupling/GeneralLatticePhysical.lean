import Decoupling.GeneralLatticeRestriction

/-!
# Physical matrix restriction for arbitrary finite-index sublattices

The entrywise multiplication matrices and their vector coordinates are
constructed in the actual coset basis. Adjoint compatibility and physical
exactness are proved for every finite-index subgroup of ℤ³.
-/

namespace Decoupling.GeneralLatticePhysical

open GeneralLatticeRestriction Matrix Module

noncomputable section

attribute [local instance] Classical.propDecidable

variable (Λ : AddSubgroup Translation) [Λ.FiniteIndex]

/-- The actual multiplication matrix in the retained residue basis. -/
def expandScalar : R →ₐ[S Λ] Matrix (Coset Λ) (Coset Λ) (S Λ) :=
  Algebra.leftMulMatrix (cosetBasis Λ)

/-- The manuscript's entry formula for the physical multiplication matrix. -/
theorem expandScalar_apply (r : R) (p q : Coset Λ) :
    expandScalar Λ r p q = τ Λ (bar (cosetBasis Λ p) * r * cosetBasis Λ q) := by
  rw [expandScalar, Algebra.leftMulMatrix_eq_repr_mul]
  change (cosetBasis Λ).coord p (r * cosetBasis Λ q) = _
  rw [← τ_inverse_mul_eq_coord, mul_assoc]

/-- Dagger over the actual retained coefficient ring. -/
def daggerS {m k : Type*} (D : Matrix m k (S Λ)) : Matrix k m (S Λ) :=
  fun i j => barS Λ (D j i)

/-- Conjugating a Laurent scalar gives the adjoint of its multiplication matrix. -/
theorem expandScalar_bar (r : R) : expandScalar Λ (bar r) = daggerS Λ (expandScalar Λ r) := by
  funext p q
  change expandScalar Λ (bar r) p q = barS Λ (expandScalar Λ r q p)
  rw [expandScalar_apply, expandScalar_apply, ← τ_bar]
  congr 1
  simp only [bar_mul, bar_bar]
  ring

/-- Physical coarse-graining expands every Laurent entry into its multiplication matrix. -/
def expandMatrix {m k : Type*} (D : Matrix m k R) :
    Matrix (m × Coset Λ) (k × Coset Λ) (S Λ) :=
  fun i j => expandScalar Λ (D i.1 j.1) i.2 j.2

@[simp] theorem expandMatrix_zero {m k : Type*} :
    expandMatrix Λ (0 : Matrix m k R) = 0 := by
  funext i j
  simp [expandMatrix]

@[simp] theorem expandMatrix_one {m : Type*} [DecidableEq m] :
    expandMatrix Λ (1 : Matrix m m R) = 1 := by
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
    expandMatrix Λ (dagger D) = daggerS Λ (expandMatrix Λ D) := by
  funext i j
  exact congrFun₂ (expandScalar_bar Λ (D j.1 i.1)) i.2 j.2

theorem expandMatrix_mul {m k l : Type*} [Fintype k]
    (D : Matrix m k R) (E : Matrix k l R) :
    expandMatrix Λ (D * E) = expandMatrix Λ D * expandMatrix Λ E := by
  funext i j
  simp [expandMatrix, Matrix.mul_apply, map_sum, Fintype.sum_prod_type, Matrix.sum_apply]

/-- Coordinates of a physical vector after retaining the coarser lattice. -/
def expandVector {m : Type*} (v : m → R) : (m × Coset Λ) → S Λ :=
  fun i => (cosetBasis Λ).coord i.2 (v i.1)

/-- The residue-coordinate change for physical vectors is an actual linear equivalence. -/
def vectorEquiv (m : Type*) : (m → R) ≃ₗ[S Λ] ((m × Coset Λ) → S Λ) where
  toFun := expandVector Λ
  invFun v i := (cosetBasis Λ).equivFun.symm (fun p => v (i, p))
  map_add' v w := by funext i; simp [expandVector]
  map_smul' s v := by funext i; simp [expandVector]
  left_inv v := by
    funext i
    exact (cosetBasis Λ).equivFun.symm_apply_apply (v i)
  right_inv v := by
    funext i
    exact congrFun ((cosetBasis Λ).equivFun.apply_symm_apply (fun p => v (i.1, p))) i.2

@[simp] theorem vectorEquiv_apply {m : Type*} (v : m → R) :
    vectorEquiv Λ m v = expandVector Λ v := rfl

/-- The expanded check matrix acts on the unchanged physical vector in residue coordinates. -/
theorem expandMatrix_mulVec {m k : Type*} [Fintype k]
    (D : Matrix m k R) (v : k → R) :
    expandMatrix Λ D *ᵥ expandVector Λ v = expandVector Λ (D *ᵥ v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, expandMatrix, expandVector]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrFun (Algebra.leftMulMatrix_mulVec_repr (cosetBasis Λ) (D i.1 j) (v j)) i.2

@[simp] theorem expandVector_eq_zero_iff {m : Type*} (v : m → R) :
    expandVector Λ v = 0 ↔ v = 0 := (vectorEquiv Λ m).map_eq_zero_iff

theorem expanded_kernel_iff {m k : Type*} [Fintype k]
    (D : Matrix m k R) (v : k → R) :
    expandMatrix Λ D *ᵥ expandVector Λ v = 0 ↔ D *ᵥ v = 0 := by
  rw [expandMatrix_mulVec, expandVector_eq_zero_iff]

theorem expanded_image_iff {k l : Type*} [Fintype l]
    (E : Matrix k l R) (v : k → R) :
    (∃ z, E *ᵥ z = v) ↔ ∃ z, expandMatrix Λ E *ᵥ z = expandVector Λ v := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨expandVector Λ z, by rw [expandMatrix_mulVec, hz]⟩
  · rintro ⟨z, hz⟩
    obtain ⟨z, rfl⟩ := (vectorEquiv Λ l).surjective z
    refine ⟨z, (vectorEquiv Λ k).injective ?_⟩
    simpa only [vectorEquiv_apply, expandMatrix_mulVec] using hz

/-- Actual physical expansion preserves exactness, hence each topological equality. -/
theorem exactness_preserved {m k l : Type*} [Fintype k] [Fintype l]
    (D : Matrix m k R) (E : Matrix k l R)
    (hexact : ∀ v, D *ᵥ v = 0 ↔ ∃ z, E *ᵥ z = v) :
    ∀ v, expandMatrix Λ D *ᵥ v = 0 ↔ ∃ z, expandMatrix Λ E *ᵥ z = v := by
  intro v
  obtain ⟨v, rfl⟩ := (vectorEquiv Λ k).surjective v
  rw [vectorEquiv_apply, expanded_kernel_iff, ← expanded_image_iff]
  exact hexact v


end
end Decoupling.GeneralLatticePhysical
