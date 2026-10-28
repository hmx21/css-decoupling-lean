import Decoupling.HighDim.FiniteLinearSolverCost
import Mathlib.LinearAlgebra.LinearIndependent.Basic
import Mathlib.LinearAlgebra.Pi

/-!
# A computed kernel basis with computed inverse coordinates

The basis vectors are columns of the actual dense solver output. Their
coordinates are read from the stored free columns. Neither direction
of the kernel parametrization uses a choice of preimages.
-/
namespace Decoupling.HighDim.FiniteLinearSolver
open ArithmeticCost Matrix
universe u
variable {K : Type u} [Field K] [DecidableEq K]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def zeroRhs (m : ℕ) : Vector K m := Vector.replicate m 0

omit [DecidableEq K] in
@[simp] theorem vector_zeroRhs (m : ℕ) : vector (zeroRhs (K := K) m) = 0 := by
  funext i
  simp [vector, zeroRhs]

omit [DecidableEq K] in
theorem zero_solves {m n : ℕ} (A : DenseMatrix K m n) : Solves A (zeroRhs m) 0 := by
  simp only [Solves, Matrix.mulVec_zero, vector_zeroRhs]

/-- Run Gaussian elimination once and retain the successful dense result
and its actual operation trace. The homogeneous system is always consistent. -/
def homogeneous {m n : ℕ} (A : DenseMatrix K m n) : Work K (Solution K n) :=
  let r := gaussian n A (zeroRhs m)
  ⟨r.value.get (gaussian_some_of_consistent A (zeroRhs m) ⟨0, zero_solves A⟩), r.trace⟩

theorem homogeneous_correct {m n : ℕ} (A : DenseMatrix K m n) :
    Correct A (zeroRhs m) (homogeneous A).value :=
  consistentSolution_correct A (zeroRhs m) ⟨0, zero_solves A⟩

theorem homogeneous_particular_zero {m n : ℕ} (A : DenseMatrix K m n) :
    vector (homogeneous A).value.particular = 0 := by
  let s := (homogeneous A).value
  have hs := homogeneous_correct A
  obtain ⟨t, ht⟩ := hs.complete 0 (zero_solves A)
  have hcoord := congrArg s.extract ht
  rw [hs.coordinates] at hcoord
  have hs0 : s.extract (0 : Fin n → K) = 0 := by funext j; rfl
  have ht0 : t = 0 := hcoord.trans hs0
  rw [ht0] at ht
  simpa only [Solution.realize, Matrix.mulVec_zero, add_zero] using ht

theorem homogeneous_realize {m n : ℕ} (A : DenseMatrix K m n)
    (t : Fin (homogeneous A).value.dimension → K) :
    (homogeneous A).value.realize t = matrix (homogeneous A).value.kernel *ᵥ t := by
  rw [Solution.realize, homogeneous_particular_zero, zero_add]

/-- Explicit coordinate equivalence with the true kernel of the input
matrix. Its inverse simply reads the computed free-column entries. -/
def kernelEquiv {m n : ℕ} (A : DenseMatrix K m n) :
    (Fin (homogeneous A).value.dimension → K) ≃ₗ[K] LinearMap.ker (matrix A).mulVecLin where
  toFun t := ⟨matrix (homogeneous A).value.kernel *ᵥ t, by
    have h := (homogeneous_correct A).sound t
    simpa only [Solves, homogeneous_realize, vector_zeroRhs, LinearMap.mem_ker,
      Matrix.mulVecLin_apply] using h⟩
  invFun x := (homogeneous A).value.extract x.1
  left_inv t := by
    have h := (homogeneous_correct A).coordinates t
    simpa only [homogeneous_realize] using h
  right_inv x := by
    apply Subtype.ext
    change matrix (homogeneous A).value.kernel *ᵥ (homogeneous A).value.extract x.1 = x.1
    obtain ⟨t, ht⟩ := (homogeneous_correct A).complete x.1 (by
      simpa only [Solves, vector_zeroRhs, LinearMap.mem_ker, Matrix.mulVecLin_apply] using x.2)
    rw [← ht, (homogeneous_correct A).coordinates]
    exact (homogeneous_realize A t).symm
  map_add' t u := by
    apply Subtype.ext
    change matrix (homogeneous A).value.kernel *ᵥ (t + u) =
      matrix (homogeneous A).value.kernel *ᵥ t + matrix (homogeneous A).value.kernel *ᵥ u
    exact Matrix.mulVec_add _ _ _
  map_smul' a t := by
    apply Subtype.ext
    change matrix (homogeneous A).value.kernel *ᵥ (a • t) = a • (matrix (homogeneous A).value.kernel *ᵥ t)
    exact Matrix.mulVec_smul _ _ _

/-- The dimension returned by the executable solver is the native
dimension of the actual kernel. -/
theorem kernel_dimension {m n : ℕ} (A : DenseMatrix K m n) :
    Module.finrank K (LinearMap.ker (matrix A).mulVecLin) = (homogeneous A).value.dimension := by
  rw [← (kernelEquiv A).finrank_eq, Module.finrank_fin_fun]

def kernelVector {m n : ℕ} (A : DenseMatrix K m n)
    (j : Fin (homogeneous A).value.dimension) : Fin n → K :=
  fun i => (homogeneous A).value.kernel[i][j]

theorem kernelVector_eq {m n : ℕ} (A : DenseMatrix K m n)
    (j : Fin (homogeneous A).value.dimension) :
    kernelVector A j = (kernelEquiv A (Pi.single j 1)).1 := by
  change kernelVector A j = matrix (homogeneous A).value.kernel *ᵥ Pi.single j 1
  rw [Matrix.mulVec_single_one]
  rfl

theorem kernelVector_independent {m n : ℕ} (A : DenseMatrix K m n) :
    LinearIndependent K (kernelVector A) := by
  let f := (LinearMap.ker (matrix A).mulVecLin).subtype.comp (kernelEquiv A).toLinearMap
  have hf : Function.Injective f := Subtype.val_injective.comp (kernelEquiv A).injective
  have hb := (Pi.basisFun K (Fin (homogeneous A).value.dimension)).linearIndependent.map' f
    (LinearMap.ker_eq_bot.mpr hf)
  have he : f ∘ (Pi.basisFun K (Fin (homogeneous A).value.dimension)) = kernelVector A := by
    funext j
    change ((kernelEquiv A) ((Pi.basisFun K (Fin (homogeneous A).value.dimension)) j)).1 = kernelVector A j
    rw [Pi.basisFun_apply]
    exact (kernelVector_eq A j).symm
  rw [he] at hb
  exact hb

theorem kernelVector_span {m n : ℕ} (A : DenseMatrix K m n) :
    Submodule.span K (Set.range (kernelVector A)) = LinearMap.ker (matrix A).mulVecLin := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    rw [kernelVector_eq]
    exact (kernelEquiv A (Pi.single j 1)).property
  · intro x hx
    let t := (kernelEquiv A).symm ⟨x, hx⟩
    have he : x = ∑ j : Fin (homogeneous A).value.dimension, t j • kernelVector A j := by
      have h := congrArg Subtype.val ((kernelEquiv A).apply_symm_apply ⟨x, hx⟩)
      change matrix (homogeneous A).value.kernel *ᵥ t = x at h
      rw [← h]
      funext i
      simp [matrix, mulVec, dotProduct, kernelVector, Finset.sum_apply, mul_comm]
    rw [he]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

/-- The returned dense columns form a basis of the genuine homogeneous
solution space, including the empty-basis case. -/
theorem kernel_basis {m n : ℕ} (A : DenseMatrix K m n) :
    LinearIndependent K (kernelVector A) ∧
      Submodule.span K (Set.range (kernelVector A)) = LinearMap.ker (matrix A).mulVecLin :=
  ⟨kernelVector_independent A, kernelVector_span A⟩

theorem homogeneous_cost {m n : ℕ} (A : DenseMatrix K m n) :
    (homogeneous A).cost ≤ 8 * (m + n + 1) ^ 4 :=
  gaussian_cost_polynomial A (zeroRhs m)

end Decoupling.HighDim.FiniteLinearSolver
