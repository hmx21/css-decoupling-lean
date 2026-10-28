import Decoupling.HighDim.PolynomialLinearSolverData

/-!
# Executable bounded polynomial linear solver

All inputs and outputs are dense field-coefficient arrays. Matrix
assembly uses shifted input lookups only. Its equality with the native
polynomial multiplication map is proved below. No assertion that the
chosen box contains every needed solution is assumed or claimed here.
-/
namespace Decoupling.HighDim.PolynomialLinearSolver
open EffectiveLinear FiniteLinearSolver ArithmeticCost MvPolynomial Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
universe u
variable {K : Type u} [Field K]

/-- Assemble a dense coefficient matrix using no field arithmetic. -/
def assemble (N d b : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d) :
    DenseMatrix K (m * boxSize N (d + b)) (n * boxSize N b) :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    let r := systemIndex N m (d + b) i
    let c := systemIndex N n b j
    shiftedLookup A[r.1][c.1] c.2.val r.2.val

theorem assembled_entry (N d b : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d)
    (i : Fin (m * boxSize N (d + b))) (j : Fin (n * boxSize N b)) :
    matrix (assemble N d b A) i j =
      coefficientMatrix (denoteMatrix A) (denoteMatrix_degree A) b
        (systemIndex N m (d + b) i) (systemIndex N n b j) := by
  classical
  simp only [matrix, assemble, Fin.getElem_fin, Vector.getElem_ofFn]
  rw [coefficientMatrix_entry_lookup]
  exact shiftedLookup_eq_coeff _ _ _

theorem assembled_matrix (N d b : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d) :
    matrix (assemble N d b A) =
      (coefficientMatrix (denoteMatrix A) (denoteMatrix_degree A) b).submatrix
        (systemIndex N m (d + b)) (systemIndex N n b) := by
  ext i j
  exact assembled_entry N d b A i j

/-- The actual polynomial action commutes with the computable dense
coefficient matrix, on every bounded polynomial vector. -/
theorem assembled_mulVec (N d b : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d)
    (y : Fin n → BoxPolynomial K N b) :
    matrix (assemble N d b A) *ᵥ denseCoordinates N n b y =
      denseCoordinates N m (d + b) (boundedMul (denoteMatrix A) (denoteMatrix_degree A) b y) := by
  classical
  rw [assembled_matrix, Matrix.submatrix_mulVec_equiv]
  have hv : (denseCoordinates N n b y) ∘ (systemIndex N n b).symm =
      vectorCoordinates K N n b y := by
    funext j
    change vectorCoordinates K N n b y ((systemIndex N n b) ((systemIndex N n b).symm j)) = _
    rw [Equiv.apply_symm_apply]
  rw [hv, coefficientMatrix_mulVec]
  rfl

noncomputable def BoundedSolves (N d b : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d)
    (v : CoeffVector K N m (d + b)) (y : Fin n → BoxPolynomial K N b) : Prop :=
  denoteMatrix A *ᵥ (fun j => (y j).val) = fun i => (denoteVector v i).val

theorem dense_solution_iff (N d b : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d)
    (v : CoeffVector K N m (d + b)) (y : Fin n → BoxPolynomial K N b) :
    Solves (assemble N d b A) (flattenVector v) (denseCoordinates N n b y) ↔
      BoundedSolves N d b A v y := by
  change matrix (assemble N d b A) *ᵥ denseCoordinates N n b y = vector (flattenVector v) ↔ _
  rw [assembled_mulVec, ← denseCoordinates_denoteVector]
  rw [(denseCoordinates (K := K) N m (d + b)).injective.eq_iff]
  constructor
  · intro h
    exact congrArg (fun z : Fin m → BoxPolynomial K N (d + b) => fun i => (z i).val) h
  · intro h
    funext i
    exact Subtype.ext (congrFun h i)

variable [DecidableEq K]

/-- The executed program: polynomial data are reduced to a dense field
matrix by index lookups, then the proved Gaussian solver is run. -/
def solveBounded (N d b : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d)
    (v : CoeffVector K N m (d + b)) : Work K (Option (Solution K (n * boxSize N b))) :=
  gaussian (n * boxSize N b) (assemble N d b A) (flattenVector v)

/-- Failure means exactly that this explicitly bounded space has no
solution. Window sufficiency for unbounded polynomial solvability is
a separate effective-degree theorem. -/
theorem solveBounded_none_iff (N d b : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d)
    (v : CoeffVector K N m (d + b)) :
    (solveBounded N d b A v).value = none ↔
      ¬ ∃ y : Fin n → BoxPolynomial K N b, BoundedSolves N d b A v y := by
  rw [solveBounded, gaussian_none_iff]
  apply not_congr
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨(denseCoordinates N n b).symm z, (dense_solution_iff N d b A v _).mp ?_⟩
    simpa only [LinearEquiv.apply_symm_apply] using hz
  · rintro ⟨y, hy⟩
    exact ⟨denseCoordinates N n b y, (dense_solution_iff N d b A v y).mpr hy⟩

/-- Every returned affine parameter gives an actual polynomial solution. -/
theorem solveBounded_sound (N d b : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d)
    (v : CoeffVector K N m (d + b)) (s : Solution K (n * boxSize N b))
    (hs : (solveBounded N d b A v).value = some s) (t : Fin s.dimension → K) :
    BoundedSolves N d b A v ((denseCoordinates N n b).symm (s.realize t)) := by
  apply (dense_solution_iff N d b A v _).mp
  rw [LinearEquiv.apply_symm_apply]
  exact (gaussian_correct (assemble N d b A) (flattenVector v) s hs).sound t

/-- Every actual bounded polynomial solution has a unique parameter in
the computed affine family. -/
theorem solveBounded_complete (N d b : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d)
    (v : CoeffVector K N m (d + b)) (s : Solution K (n * boxSize N b))
    (hs : (solveBounded N d b A v).value = some s)
    (y : Fin n → BoxPolynomial K N b) (hy : BoundedSolves N d b A v y) :
    ∃! t : Fin s.dimension → K, (denseCoordinates N n b).symm (s.realize t) = y := by
  have hc := gaussian_correct (assemble N d b A) (flattenVector v) s hs
  obtain ⟨t, ht⟩ := hc.complete _ ((dense_solution_iff N d b A v y).mpr hy)
  refine ⟨t, ?_, ?_⟩
  · change (denseCoordinates N n b).symm (s.realize t) = y
    rw [ht, LinearEquiv.symm_apply_apply]
  · intro u hu
    apply hc.injective
    apply (denseCoordinates N n b).symm.injective
    rw [hu, ht, LinearEquiv.symm_apply_apply]

/-- Cost of the actual field operation trace. Matrix assembly performs
only natural-number indexing and reads of dense input coefficients. -/
theorem solveBounded_cost (N d b : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d)
    (v : CoeffVector K N m (d + b)) :
    (solveBounded N d b A v).cost ≤
      8 * (m * (d + b + 1) ^ N + n * (b + 1) ^ N + 1) ^ 4 :=
  gaussian_cost_polynomial (assemble N d b A) (flattenVector v)

end Decoupling.HighDim.PolynomialLinearSolver
