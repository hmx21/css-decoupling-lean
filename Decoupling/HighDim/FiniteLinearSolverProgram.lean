import Decoupling.HighDim.FiniteLinearSolverSteps

/-!
# Executable, trace-instrumented Gaussian elimination

Only dense arrays of already computed field values are retained between
steps. Every field arithmetic instruction and every pivot zero test
passes through the instrumented primitive operations. In particular,
the complexity proof cannot rely on lazily recomputing function matrices.
-/
namespace Decoupling.HighDim.FiniteLinearSolver
open ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
universe u
variable {K : Type u} [Field K] [DecidableEq K]

def eliminateProgram {m n : ℕ} (A : DenseMatrix K m (n + 1)) (b : Vector K m) (r : Fin m) :
    Work K (DenseMatrix K m n × Vector K m) :=
  Work.bind (collect m (fun i => ArithmeticCost.div A[i][0] A[r][0])) fun ratios =>
    Work.bind (collect m (fun i => collect n (fun j =>
      Work.bind (ArithmeticCost.mul ratios[i] A[r][j.succ]) fun z => ArithmeticCost.sub A[i][j.succ] z))) fun C =>
        Work.bind (collect m (fun i =>
          Work.bind (ArithmeticCost.mul ratios[i] b[r]) fun z => ArithmeticCost.sub b[i] z)) fun d =>
            Work.pure (C, d)

def pivotProgram {m n : ℕ} (A : DenseMatrix K m (n + 1)) (b : Vector K m)
    (r : Fin m) (s : Solution K n) : Work K (Solution K (n + 1)) :=
  Work.bind (dot n (fun i => A[r][i.succ]) (vector s.particular)) fun d =>
    Work.bind (ArithmeticCost.sub b[r] d) fun z =>
      Work.bind (ArithmeticCost.div z A[r][0]) fun head =>
        Work.bind (collect s.dimension (fun j =>
          Work.bind (dot n (fun i => A[r][i.succ]) (fun i => s.kernel[i][j])) fun d =>
            Work.bind (ArithmeticCost.neg d) fun e => ArithmeticCost.div e A[r][0])) fun row =>
              Work.pure {
                dimension := s.dimension
                particular := prepend head s.particular
                kernel := prepend row s.kernel
                freeColumns := s.freeColumns.map Fin.succ }

/-- The solver terminates by the strictly decreasing number of columns.
`none` is an inconsistency answer; `some` contains all affine solutions. -/
def gaussian : (n : ℕ) → {m : ℕ} → DenseMatrix K m n → Vector K m → Work K (Option (Solution K n))
  | 0, m, _, b => Work.bind (firstNonzero m (vector b)) fun r =>
      Work.pure (match r with | none => some emptySolution | some _ => none)
  | n + 1, m, A, b => Work.bind (firstNonzero m (fun i => A[i][0])) fun r =>
      match r with
      | none => Work.bind (gaussian n (tailMatrix A) b) fun s => Work.pure (s.map freeExtend)
      | some r => Work.bind (eliminateProgram A b r) fun e =>
          Work.bind (gaussian n e.1 e.2) fun s =>
            match s with
            | none => Work.pure none
            | some s => Work.bind (pivotProgram A b r s) fun t => Work.pure (some t)

omit [Field K] [DecidableEq K] in
theorem vector_ext {α : Type*} {n : ℕ} {v w : Vector α n}
    (h : ∀ i : Fin n, v[i] = w[i]) : v = w := Vector.ext (fun i hi => h ⟨i, hi⟩)

omit [DecidableEq K] in
@[simp] theorem eliminateProgram_value {m n : ℕ} (A : DenseMatrix K m (n + 1)) (b : Vector K m)
    (r : Fin m) : (eliminateProgram A b r).value = (eliminatedMatrix A r, eliminatedRhs A b r) := by
  apply Prod.ext
  · apply vector_ext
    intro i
    apply vector_ext
    intro j
    simp [eliminateProgram, eliminatedMatrix]
  · apply vector_ext
    intro i
    simp [eliminateProgram, eliminatedRhs]

omit [DecidableEq K] in
@[simp] theorem pivotProgram_value {m n : ℕ} (A : DenseMatrix K m (n + 1)) (b : Vector K m)
    (r : Fin m) (s : Solution K n) : (pivotProgram A b r s).value = pivotExtend A b r s := by
  simp only [pivotProgram, Work.bind_value, Work.pure_value, dot_value,
    sub_value, div_value, pivotExtend, pivotHead]
  congr 1
  apply congrArg (fun row => prepend row s.kernel)
  apply vector_ext
  intro j
  simp

end Decoupling.HighDim.FiniteLinearSolver
