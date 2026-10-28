import Decoupling.HighDim.PolynomialLinearSolverComplete

/-!
# Computed generators of the full polynomial kernel

The actual Gaussian columns in the proved cutoff box generate the
entire polynomial-module kernel. In particular, this conclusion is
not restricted to the bounded vector space used during elimination.
-/
namespace Decoupling.HighDim.PolynomialLinearSolver
open EffectiveLinear FiniteLinearSolver ArithmeticCost Matrix MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u
variable {K : Type u} [Field K] [DecidableEq K]

def kernelComplete (N d : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d) :
    Work K (Solution K (n * boxSize N (completeCutoff N m d))) :=
  kernelBounded N d (completeCutoff N m d) A

/-- Native polynomial meaning of an actual returned coefficient column. -/
noncomputable def polynomialKernelVector (N d : ℕ) {m n : ℕ}
    (A : CoeffMatrix K N m n d) (j : Fin (kernelComplete N d A).value.dimension) :
    Fin n → MvPolynomial (Fin N) K :=
  fun i => (boundedKernelVector N d (completeCutoff N m d) A j i).val

theorem polynomialKernelVector_mem (N d : ℕ) {m n : ℕ}
    (A : CoeffMatrix K N m n d) (j : Fin (kernelComplete N d A).value.dimension) :
    polynomialKernelVector N d A j ∈ LinearMap.ker (denoteMatrix A).mulVecLin := by
  have h := (boundedKernelEquiv N d (completeCutoff N m d) A (Pi.single j 1)).property
  rw [← boundedKernelVector_eq] at h
  exact congrArg (fun z : Fin m → BoxPolynomial K N (d + completeCutoff N m d) =>
    fun i => (z i).val) h

theorem bounded_kernel_expansion (N d b : ℕ) {m n : ℕ}
    (A : CoeffMatrix K N m n d)
    (y : LinearMap.ker (boundedMul (denoteMatrix A) (denoteMatrix_degree A) b)) :
    ∃ t : Fin (kernelBounded N d b A).value.dimension → K,
      (fun i => (y.val i).val) =
        ∑ j, (C (t j) : MvPolynomial (Fin N) K) •
          (fun i => (boundedKernelVector N d b A j i).val) := by
  let t := (boundedKernelEquiv N d b A).symm y
  refine ⟨t, ?_⟩
  have ht : t = ∑ j, t j • Pi.single j (1 : K) := by
    funext i
    simp [Finset.sum_apply, Pi.single_apply]
  have h := congrArg (fun z : LinearMap.ker
      (boundedMul (denoteMatrix A) (denoteMatrix_degree A) b) => fun i => (z.val i).val)
    ((boundedKernelEquiv N d b A).apply_symm_apply y)
  change (fun i => ((boundedKernelEquiv N d b A t).val i).val) = _ at h
  rw [ht, map_sum] at h
  rw [← h]
  funext i
  simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply,
    Pi.smul_apply, ← boundedKernelVector_eq]
  simp [Algebra.smul_def]

/-- The computed finite family generates the full native polynomial
kernel, including all solutions outside the search box. -/
theorem polynomialKernelVector_span (N d : ℕ) {m n : ℕ}
    (A : CoeffMatrix K N m n d) :
    Submodule.span (MvPolynomial (Fin N) K) (Set.range (polynomialKernelVector N d A)) =
      LinearMap.ker (denoteMatrix A).mulVecLin := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (by
      rintro _ ⟨j, rfl⟩
      exact polynomialKernelVector_mem N d A j)
  · rw [Hermann.kernel_generation_common (denoteMatrix A)
      (fun i j => boxed_totalDegree (denotePolynomial N d A[i][j]))]
    apply Submodule.span_le.mpr
    intro y hy
    let z : Fin n → BoxPolynomial K N (completeCutoff N m d) :=
      fun i => ⟨y i, mem_box_of_totalDegree_le (hy.2 i)⟩
    have hz : z ∈ LinearMap.ker
        (boundedMul (denoteMatrix A) (denoteMatrix_degree A) (completeCutoff N m d)) := by
      apply funext
      intro i
      apply Subtype.ext
      exact congrFun hy.1 i
    obtain ⟨t, ht⟩ := bounded_kernel_expansion N d (completeCutoff N m d) A ⟨z, hz⟩
    change y = ∑ j, C (t j) • polynomialKernelVector N d A j at ht
    rw [ht]
    exact Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))

theorem kernelComplete_number_le (N d : ℕ) {m n : ℕ}
    (A : CoeffMatrix K N m n d) :
    (kernelComplete N d A).value.dimension ≤ n * (completeCutoff N m d + 1) ^ N :=
  (homogeneous_correct (assemble N d (completeCutoff N m d) A)).dimension_le

theorem polynomialKernelVector_degree (N d : ℕ) {m n : ℕ}
    (A : CoeffMatrix K N m n d) (j : Fin (kernelComplete N d A).value.dimension) (i : Fin n) :
    (polynomialKernelVector N d A j i).totalDegree ≤ N * completeCutoff N m d :=
  boxed_totalDegree _

theorem kernelComplete_cost (N d : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d) :
    (kernelComplete N d A).cost ≤
      8 * (m * (d + completeCutoff N m d + 1) ^ N +
        n * (completeCutoff N m d + 1) ^ N + 1) ^ 4 :=
  kernelBounded_cost N d (completeCutoff N m d) A

/-- Every unbounded solution is the returned particular solution plus
a polynomial combination of the computed full-kernel generators. -/
theorem complete_affine_solution_iff (N d : ℕ) {m n : ℕ}
    (A : CoeffMatrix K N m n d) (v : CoeffVector K N m d)
    (s : Solution K (n * boxSize N (completeCutoff N m d)))
    (hs : (solveComplete N d A v).value = some s)
    (y : Fin n → MvPolynomial (Fin N) K) :
    denoteMatrix A *ᵥ y = (fun i => (denoteVector v i).val) ↔
      y - (fun j => ((denseCoordinates N n (completeCutoff N m d)).symm (s.realize 0) j).val) ∈
        Submodule.span (MvPolynomial (Fin N) K) (Set.range (polynomialKernelVector N d A)) := by
  rw [polynomialKernelVector_span]
  change _ ↔ denoteMatrix A *ᵥ
    (y - fun j => ((denseCoordinates N n (completeCutoff N m d)).symm (s.realize 0) j).val) = 0
  rw [Matrix.mulVec_sub, solveComplete_sound N d A v s hs 0, sub_eq_zero]

end Decoupling.HighDim.PolynomialLinearSolver
