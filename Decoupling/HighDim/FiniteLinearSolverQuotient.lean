import Decoupling.HighDim.FiniteLinearSolverKernel
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Computed representatives for a finite-dimensional quotient

For a supplied matrix U, execute the kernel algorithm on U transpose.
Its free column indices specify standard vectors in the original
codomain. Their quotient classes form a basis of the actual cokernel.
Both the representatives and the coordinate projection are extracted
from the executed Gaussian result.
-/
namespace Decoupling.HighDim.FiniteLinearSolver
open ArithmeticCost Matrix
universe u
variable {K : Type u} [Field K] [DecidableEq K]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def transposeDense {m n : ℕ} (A : DenseMatrix K m n) : DenseMatrix K n m :=
  Vector.ofFn fun j => Vector.ofFn fun i => A[i][j]

omit [Field K] [DecidableEq K] in
@[simp] theorem matrix_transposeDense {m n : ℕ} (A : DenseMatrix K m n) :
    matrix (transposeDense A) = (matrix A).transpose := by
  funext i j
  simp [matrix, transposeDense]

def quotientData {g r : ℕ} (U : DenseMatrix K g r) : Work K (Solution K g) :=
  homogeneous (transposeDense U)

def quotientProjection {g r : ℕ} (U : DenseMatrix K g r) :
    (Fin g → K) →ₗ[K] (Fin (quotientData U).value.dimension → K) :=
  (matrix (quotientData U).value.kernel).transpose.mulVecLin

def quotientRepresentative {g r : ℕ} (U : DenseMatrix K g r)
    (j : Fin (quotientData U).value.dimension) : Fin g → K :=
  Pi.single (quotientData U).value.freeColumns[j] 1

theorem quotientProjection_representative {g r : ℕ} (U : DenseMatrix K g r)
    (j : Fin (quotientData U).value.dimension) :
    quotientProjection U (quotientRepresentative U j) = Pi.single j 1 := by
  funext i
  have hj := (homogeneous_correct (transposeDense U)).coordinates (Pi.single i 1)
  rw [homogeneous_realize, Matrix.mulVec_single_one] at hj
  have hij := congrFun hj j
  change (quotientData U).value.kernel[(quotientData U).value.freeColumns[j]][i] =
    (Pi.single i (1 : K) : Fin (quotientData U).value.dimension → K) j at hij
  simp only [quotientProjection, Matrix.mulVecLin_apply, quotientRepresentative, Matrix.mulVec_single_one,
    Matrix.col, Matrix.transpose_apply, matrix]
  rw [hij]
  simp [Pi.single_apply, eq_comm]

def quotientSection {g r : ℕ} (U : DenseMatrix K g r) :
    (Fin (quotientData U).value.dimension → K) →ₗ[K] (Fin g → K) where
  toFun t := ∑ j, t j • quotientRepresentative U j
  map_add' t v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a t := by simp [mul_smul, Finset.smul_sum]

theorem quotientProjection_section {g r : ℕ} (U : DenseMatrix K g r)
    (t : Fin (quotientData U).value.dimension → K) :
    quotientProjection U (quotientSection U t) = t := by
  simp only [quotientSection, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul,
    quotientProjection_representative]
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

theorem quotientProjection_surjective {g r : ℕ} (U : DenseMatrix K g r) :
    Function.Surjective (quotientProjection U) :=
  fun t => ⟨quotientSection U t, quotientProjection_section U t⟩

theorem range_le_quotientProjection_ker {g r : ℕ} (U : DenseMatrix K g r) :
    LinearMap.range (matrix U).mulVecLin ≤ LinearMap.ker (quotientProjection U) := by
  rintro _ ⟨v, rfl⟩
  change (matrix (quotientData U).value.kernel).transpose *ᵥ (matrix U *ᵥ v) = 0
  rw [Matrix.mulVec_mulVec]
  have hzero : (matrix U).transpose * matrix (quotientData U).value.kernel = 0 := by
    ext i j
    have h := (kernelEquiv (transposeDense U) (Pi.single j 1)).property
    change matrix (transposeDense U) *ᵥ
      (matrix (quotientData U).value.kernel *ᵥ Pi.single j 1) = 0 at h
    rw [matrix_transposeDense, Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
    exact congrFun h i
  have ht := congrArg Matrix.transpose hzero
  rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_zero] at ht
  rw [ht, Matrix.zero_mulVec]

theorem quotientProjection_ker {g r : ℕ} (U : DenseMatrix K g r) :
    LinearMap.ker (quotientProjection U) = LinearMap.range (matrix U).mulVecLin := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq (range_le_quotientProjection_ker U)
  have hU := LinearMap.finrank_range_add_finrank_ker (matrix (transposeDense U)).mulVecLin
  rw [kernel_dimension, Module.finrank_fin_fun, matrix_transposeDense] at hU
  have hr : Module.finrank K (LinearMap.range (matrix U).transpose.mulVecLin) =
      Module.finrank K (LinearMap.range (matrix U).mulVecLin) := Matrix.rank_transpose (matrix U)
  rw [hr] at hU
  have hP := LinearMap.finrank_range_add_finrank_ker (quotientProjection U)
  rw [LinearMap.range_eq_top.mpr (quotientProjection_surjective U),
    finrank_top, Module.finrank_fin_fun, Module.finrank_fin_fun] at hP
  change Module.finrank K (LinearMap.range (matrix U).mulVecLin) +
    (quotientData U).value.dimension = g at hU
  omega

def quotientEquiv {g r : ℕ} (U : DenseMatrix K g r) :
    ((Fin g → K) ⧸ LinearMap.range (matrix U).mulVecLin) ≃ₗ[K]
      (Fin (quotientData U).value.dimension → K) where
  toFun := (LinearMap.range (matrix U).mulVecLin).liftQ (quotientProjection U)
    (range_le_quotientProjection_ker U)
  invFun t := (LinearMap.range (matrix U).mulVecLin).mkQ (quotientSection U t)
  left_inv x := by
    induction x using Submodule.Quotient.induction_on with
    | H x =>
      apply (Submodule.Quotient.eq _).mpr
      change quotientSection U (quotientProjection U x) - x ∈ LinearMap.range (matrix U).mulVecLin
      rw [← quotientProjection_ker]
      change quotientProjection U (quotientSection U (quotientProjection U x) - x) = 0
      rw [map_sub, quotientProjection_section, sub_self]
  right_inv t := quotientProjection_section U t
  map_add' x y := map_add _ _ _
  map_smul' a x := map_smul _ _ _

theorem quotientEquiv_representative {g r : ℕ} (U : DenseMatrix K g r)
    (j : Fin (quotientData U).value.dimension) :
    quotientEquiv U ((LinearMap.range (matrix U).mulVecLin).mkQ (quotientRepresentative U j)) =
      Pi.single j 1 :=
  quotientProjection_representative U j

/-- A native basis whose vectors are exactly the computed standard
representatives. This packaging does not select new representatives. -/
noncomputable def quotientBasis {g r : ℕ} (U : DenseMatrix K g r) :
    Module.Basis (Fin (quotientData U).value.dimension) K
      ((Fin g → K) ⧸ LinearMap.range (matrix U).mulVecLin) :=
  (Pi.basisFun K _).map (quotientEquiv U).symm

theorem quotientBasis_apply {g r : ℕ} (U : DenseMatrix K g r)
    (j : Fin (quotientData U).value.dimension) :
    quotientBasis U j =
      (LinearMap.range (matrix U).mulVecLin).mkQ (quotientRepresentative U j) := by
  apply (quotientEquiv U).injective
  rw [quotientEquiv_representative]
  change quotientEquiv U ((quotientEquiv U).symm (Pi.basisFun K _ j)) = _
  rw [LinearEquiv.apply_symm_apply, Pi.basisFun_apply]

theorem quotient_dimension {g r : ℕ} (U : DenseMatrix K g r) :
    Module.finrank K ((Fin g → K) ⧸ LinearMap.range (matrix U).mulVecLin) =
      (quotientData U).value.dimension := by
  rw [(quotientEquiv U).finrank_eq, Module.finrank_fin_fun]

theorem quotientData_cost {g r : ℕ} (U : DenseMatrix K g r) :
    (quotientData U).cost ≤ 8 * (r + g + 1) ^ 4 :=
  homogeneous_cost (transposeDense U)

end Decoupling.HighDim.FiniteLinearSolver
