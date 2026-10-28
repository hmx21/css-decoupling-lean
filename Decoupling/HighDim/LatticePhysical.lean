import Decoupling.HighDim.LatticeRestriction

/-!
# Physical matrix restriction for arbitrary finite-index sublattices

The entrywise multiplication matrices and their vector coordinates are
constructed in the actual coset basis. Adjoint compatibility and physical
exactness are proved for every finite-index subgroup of ℤ^D over an arbitrary commutative ring.
Source: `drafts/appendix.tex:263–306`; retained coefficients are the literal
subgroup-algebra subring, and expansion uses an actual linear basis.
-/

namespace Decoupling.HighDim.LatticePhysical

open LatticeRestriction Matrix Module

noncomputable section

attribute [local instance] Classical.propDecidable

variable (K : Type*) [CommRing K] {D : ℕ}

variable (Λ : AddSubgroup (Translation D)) [Λ.FiniteIndex]

/-- The actual multiplication matrix in the retained residue basis. -/
def expandScalar : (Laurent K D) →ₐ[S K Λ] Matrix (Coset Λ) (Coset Λ) (S K Λ) :=
  Algebra.leftMulMatrix (cosetBasis K Λ)

/-- The manuscript's entry formula for the physical multiplication matrix. -/
theorem expandScalar_apply (r : (Laurent K D)) (p q : Coset Λ) :
    expandScalar K Λ r p q = τ K Λ (bar (cosetBasis K Λ p) * r * cosetBasis K Λ q) := by
  rw [expandScalar, Algebra.leftMulMatrix_eq_repr_mul]
  change (cosetBasis K Λ).coord p (r * cosetBasis K Λ q) = _
  rw [← τ_inverse_mul_eq_coord, mul_assoc]

/-- Dagger over the actual retained coefficient ring. -/
def daggerS {m k : Type*} (A : Matrix m k (S K Λ)) : Matrix k m (S K Λ) :=
  fun i j => barS K Λ (A j i)

/-- Conjugating a Laurent scalar gives the adjoint of its multiplication matrix. -/
theorem expandScalar_bar (r : (Laurent K D)) : expandScalar K Λ (bar r) = daggerS K Λ (expandScalar K Λ r) := by
  funext p q
  change expandScalar K Λ (bar r) p q = barS K Λ (expandScalar K Λ r q p)
  rw [expandScalar_apply, expandScalar_apply, ← τ_bar]
  congr 1
  simp only [bar_mul, bar_bar]
  ring

/-- Physical coarse-graining expands every Laurent entry into its multiplication matrix. -/
def expandMatrix {m k : Type*} (A : Matrix m k (Laurent K D)) :
    Matrix (m × Coset Λ) (k × Coset Λ) (S K Λ) :=
  fun i j => expandScalar K Λ (A i.1 j.1) i.2 j.2

@[simp] theorem expandMatrix_zero {m k : Type*} :
    expandMatrix K Λ (0 : Matrix m k (Laurent K D)) = 0 := by
  funext i j
  simp [expandMatrix]

@[simp] theorem expandMatrix_one {m : Type*} [DecidableEq m] :
    expandMatrix K Λ (1 : Matrix m m (Laurent K D)) = 1 := by
  classical
  funext i j
  rcases i with ⟨i, p⟩
  rcases j with ⟨j, q⟩
  by_cases hij : i = j
  · subst j
    simp [expandMatrix, Matrix.one_apply]
  · simp [expandMatrix, hij]

/-- Dagger commutes with the actual physical matrix expansion, including rectangular matrices. -/
theorem expandMatrix_dagger {m k : Type*} (A : Matrix m k (Laurent K D)) :
    expandMatrix K Λ (dagger A) = daggerS K Λ (expandMatrix K Λ A) := by
  funext i j
  exact congrFun₂ (expandScalar_bar K Λ (A j.1 i.1)) i.2 j.2

theorem expandMatrix_mul {m k l : Type*} [Fintype k]
    (A : Matrix m k (Laurent K D)) (E : Matrix k l (Laurent K D)) :
    expandMatrix K Λ (A * E) = expandMatrix K Λ A * expandMatrix K Λ E := by
  funext i j
  simp [expandMatrix, Matrix.mul_apply, map_sum, Fintype.sum_prod_type, Matrix.sum_apply]

/-- Coordinates of a physical vector after retaining the coarser lattice. -/
def expandVector {m : Type*} (v : m → (Laurent K D)) : (m × Coset Λ) → S K Λ :=
  fun i => (cosetBasis K Λ).coord i.2 (v i.1)

/-- The residue-coordinate change for physical vectors is an actual linear equivalence. -/
def vectorEquiv (m : Type*) : (m → (Laurent K D)) ≃ₗ[S K Λ] ((m × Coset Λ) → S K Λ) where
  toFun := expandVector K Λ
  invFun v i := (cosetBasis K Λ).equivFun.symm (fun p => v (i, p))
  map_add' v w := by funext i; simp [expandVector]
  map_smul' s v := by funext i; simp [expandVector]
  left_inv v := by
    funext i
    exact (cosetBasis K Λ).equivFun.symm_apply_apply (v i)
  right_inv v := by
    funext i
    exact congrFun ((cosetBasis K Λ).equivFun.apply_symm_apply (fun p => v (i.1, p))) i.2

@[simp] theorem vectorEquiv_apply {m : Type*} (v : m → (Laurent K D)) :
    vectorEquiv K Λ m v = expandVector K Λ v := rfl

/-- The expanded check matrix acts on the unchanged physical vector in residue coordinates. -/
theorem expandMatrix_mulVec {m k : Type*} [Fintype k]
    (A : Matrix m k (Laurent K D)) (v : k → (Laurent K D)) :
    expandMatrix K Λ A *ᵥ expandVector K Λ v = expandVector K Λ (A *ᵥ v) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, expandMatrix, expandVector]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact congrFun (Algebra.leftMulMatrix_mulVec_repr (cosetBasis K Λ) (A i.1 j) (v j)) i.2

@[simp] theorem expandVector_eq_zero_iff {m : Type*} (v : m → (Laurent K D)) :
    expandVector K Λ v = 0 ↔ v = 0 := (vectorEquiv K Λ m).map_eq_zero_iff

theorem expanded_kernel_iff {m k : Type*} [Fintype k]
    (A : Matrix m k (Laurent K D)) (v : k → (Laurent K D)) :
    expandMatrix K Λ A *ᵥ expandVector K Λ v = 0 ↔ A *ᵥ v = 0 := by
  rw [expandMatrix_mulVec, expandVector_eq_zero_iff]

theorem expanded_image_iff {k l : Type*} [Fintype l]
    (E : Matrix k l (Laurent K D)) (v : k → (Laurent K D)) :
    (∃ z, E *ᵥ z = v) ↔ ∃ z, expandMatrix K Λ E *ᵥ z = expandVector K Λ v := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨expandVector K Λ z, by rw [expandMatrix_mulVec, hz]⟩
  · rintro ⟨z, hz⟩
    obtain ⟨z, rfl⟩ := (vectorEquiv K Λ l).surjective z
    refine ⟨z, (vectorEquiv K Λ k).injective ?_⟩
    simpa only [vectorEquiv_apply, expandMatrix_mulVec] using hz

/-- Actual physical expansion preserves exactness, hence each topological equality. -/
theorem exactness_preserved {m k l : Type*} [Fintype k] [Fintype l]
    (A : Matrix m k (Laurent K D)) (E : Matrix k l (Laurent K D))
    (hexact : ∀ v, A *ᵥ v = 0 ↔ ∃ z, E *ᵥ z = v) :
    ∀ v, expandMatrix K Λ A *ᵥ v = 0 ↔ ∃ z, expandMatrix K Λ E *ᵥ z = v := by
  intro v
  obtain ⟨v, rfl⟩ := (vectorEquiv K Λ k).surjective v
  rw [vectorEquiv_apply, expanded_kernel_iff, ← expanded_image_iff]
  exact hexact v


end
end Decoupling.HighDim.LatticePhysical
