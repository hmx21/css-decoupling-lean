import Decoupling.HighDim.PolynomialLinearSolverProgram

/-!
# Computed bases of bounded polynomial kernels

The program returns dense coefficient columns. The equivalence below
identifies those columns with the kernel of actual polynomial
multiplication on the stated coefficient box. This is a vector-space
basis of the bounded kernel; global module generation requires the
separate effective degree bound.
-/
namespace Decoupling.HighDim.PolynomialLinearSolver
open EffectiveLinear FiniteLinearSolver ArithmeticCost Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
universe u
variable {K : Type u} [Field K]

/-- Coefficient reindexing identifies the two genuine kernels. -/
noncomputable def kernelCoordinateEquiv (N d b : ℕ) {m n : ℕ}
    (A : CoeffMatrix K N m n d) :
    LinearMap.ker (matrix (assemble N d b A)).mulVecLin ≃ₗ[K]
      LinearMap.ker (boundedMul (denoteMatrix A) (denoteMatrix_degree A) b) where
  toFun x := ⟨(denseCoordinates N n b).symm x.val, by
    apply (denseCoordinates N m (d + b)).injective
    rw [map_zero, ← assembled_mulVec, LinearEquiv.apply_symm_apply]
    exact x.property⟩
  invFun y := ⟨denseCoordinates N n b y.val, by
    change matrix (assemble N d b A) *ᵥ denseCoordinates N n b y.val = 0
    rw [assembled_mulVec, show boundedMul (denoteMatrix A) (denoteMatrix_degree A) b y.val = 0
      from y.property, map_zero]⟩
  left_inv x := by apply Subtype.ext; exact LinearEquiv.apply_symm_apply _ _
  right_inv y := by apply Subtype.ext; exact LinearEquiv.symm_apply_apply _ _
  map_add' x y := by apply Subtype.ext; exact map_add _ _ _
  map_smul' a x := by apply Subtype.ext; exact map_smul _ _ _

variable [DecidableEq K]

/-- Execute the homogeneous solver on the assembled lookup matrix. -/
def kernelBounded (N d b : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d) :
    Work K (Solution K (n * boxSize N b)) :=
  homogeneous (assemble N d b A)

/-- The computed free coordinates parametrise exactly the native
bounded polynomial kernel, with no choice of a basis or preimages. -/
noncomputable def boundedKernelEquiv (N d b : ℕ) {m n : ℕ}
    (A : CoeffMatrix K N m n d) :
    (Fin (kernelBounded N d b A).value.dimension → K) ≃ₗ[K]
      LinearMap.ker (boundedMul (denoteMatrix A) (denoteMatrix_degree A) b) :=
  (kernelEquiv (assemble N d b A)).trans (kernelCoordinateEquiv N d b A)

noncomputable def boundedKernelVector (N d b : ℕ) {m n : ℕ}
    (A : CoeffMatrix K N m n d) (j : Fin (kernelBounded N d b A).value.dimension) :
    Fin n → BoxPolynomial K N b :=
  (denseCoordinates N n b).symm (kernelVector (assemble N d b A) j)

theorem boundedKernelVector_eq (N d b : ℕ) {m n : ℕ}
    (A : CoeffMatrix K N m n d) (j : Fin (kernelBounded N d b A).value.dimension) :
    boundedKernelVector N d b A j = (boundedKernelEquiv N d b A (Pi.single j 1)).val := by
  change (denseCoordinates N n b).symm (kernelVector (assemble N d b A) j) =
    (denseCoordinates N n b).symm (kernelEquiv (assemble N d b A) (Pi.single j 1)).val
  rw [kernelVector_eq]

theorem boundedKernelVector_independent (N d b : ℕ) {m n : ℕ}
    (A : CoeffMatrix K N m n d) :
    LinearIndependent K (boundedKernelVector N d b A) := by
  let f := (LinearMap.ker (boundedMul (denoteMatrix A) (denoteMatrix_degree A) b)).subtype.comp
    (boundedKernelEquiv N d b A).toLinearMap
  have hf : Function.Injective f := Subtype.val_injective.comp (boundedKernelEquiv N d b A).injective
  have hb := (Pi.basisFun K (Fin (kernelBounded N d b A).value.dimension)).linearIndependent.map' f
    (LinearMap.ker_eq_bot.mpr hf)
  have he : f ∘ Pi.basisFun K (Fin (kernelBounded N d b A).value.dimension) =
      boundedKernelVector N d b A := by
    funext j
    change (boundedKernelEquiv N d b A (Pi.basisFun K _ j)).val = _
    rw [Pi.basisFun_apply]
    exact (boundedKernelVector_eq N d b A j).symm
  rw [he] at hb
  exact hb

theorem boundedKernelVector_span (N d b : ℕ) {m n : ℕ}
    (A : CoeffMatrix K N m n d) :
    Submodule.span K (Set.range (boundedKernelVector N d b A)) =
      LinearMap.ker (boundedMul (denoteMatrix A) (denoteMatrix_degree A) b) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨j, rfl⟩
    rw [boundedKernelVector_eq]
    exact (boundedKernelEquiv N d b A (Pi.single j 1)).property
  · intro x hx
    let t := (boundedKernelEquiv N d b A).symm ⟨x, hx⟩
    have ht : t = ∑ j, t j • Pi.single j (1 : K) := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply]
    have he : x = ∑ j, t j • boundedKernelVector N d b A j := by
      have h := congrArg Subtype.val ((boundedKernelEquiv N d b A).apply_symm_apply ⟨x, hx⟩)
      change (boundedKernelEquiv N d b A t).val = x at h
      rw [ht, map_sum] at h
      simpa only [map_smul, Submodule.coe_sum, Submodule.coe_smul,
        ← boundedKernelVector_eq] using h.symm
    rw [he]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

/-- Native dimension of the bounded kernel equals the computed rank. -/
theorem boundedKernel_dimension (N d b : ℕ) {m n : ℕ}
    (A : CoeffMatrix K N m n d) :
    Module.finrank K (LinearMap.ker (boundedMul (denoteMatrix A) (denoteMatrix_degree A) b)) =
      (kernelBounded N d b A).value.dimension := by
  rw [← (boundedKernelEquiv N d b A).finrank_eq, Module.finrank_fin_fun]

theorem kernelBounded_cost (N d b : ℕ) {m n : ℕ}
    (A : CoeffMatrix K N m n d) :
    (kernelBounded N d b A).cost ≤
      8 * (m * (d + b + 1) ^ N + n * (b + 1) ^ N + 1) ^ 4 :=
  homogeneous_cost (assemble N d b A)

end Decoupling.HighDim.PolynomialLinearSolver
