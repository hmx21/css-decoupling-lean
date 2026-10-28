import Decoupling.HighDim.LaurentArithmeticProgram
import Decoupling.HighDim.FiniteLinearSolverData

/-!
# HD012 executable dense Laurent matrix formulas and their arithmetic cost

Products and sums materialize the intermediate coefficient arrays. Every
field operation is inherited from the proved scalar programs, so copying
blocks and reading array entries cannot hide repeated multiplication.
-/
namespace Decoupling.HighDim.LaurentArithmetic
open ArithmeticCost Matrix
variable {K : Type*} [Field K] {D a b h m n r : ℕ}
set_option backward.isDefEq.respectTransparency false

def sumValues : (n : ℕ) → (Fin n → K) → Work K K
  | 0, _ => Work.pure 0
  | n + 1, v => Work.bind (sumValues n (fun i => v i.succ)) fun s =>
      ArithmeticCost.add (v 0) s

@[simp] theorem sumValues_value : ∀ n (v : Fin n → K),
    (sumValues n v).value = ∑ i, v i := by
  intro n
  induction n with
  | zero => intro v; simp [sumValues]
  | succ n ih => intro v; simp [sumValues, ih, Fin.sum_univ_succ]

@[simp] theorem sumValues_cost : ∀ n (v : Fin n → K),
    (sumValues n v).cost = n := by
  intro n
  induction n with
  | zero => intro v; rfl
  | succ n ih => intro v; simp [sumValues, ih]

def sumProgram (v : Vector (Dense K D h) n) : Work K (Dense K D h) :=
  collect (boxSize D h) fun k => sumValues n (fun i => v[i][k])

@[simp] theorem sumProgram_cost (v : Vector (Dense K D h) n) :
    (sumProgram v).cost = boxSize D h * n := by simp [sumProgram]

theorem sumProgram_correct (v : Vector (Dense K D h) n) :
    denote (sumProgram v).value = ∑ i : Fin n, denote v[i] := by
  apply denote_eq_of_coeff
  · exact LaurentBoxes.supported_sum _ _ (fun i _ => denote_supported v[i])
  · intro k
    simp [sumProgram, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, denote_coeff]

abbrev DenseMatrix (K : Type*) (D m n h : ℕ) :=
  Vector (Vector (Dense K D h) n) m

noncomputable def matrixDenote (A : DenseMatrix K D m n h) :
    Matrix (Fin m) (Fin n) (Laurent K D) := fun i j => denote A[i][j]

theorem matrixDenote_supported (A : DenseMatrix K D m n h) :
    LaurentBoxes.MatrixSupported (matrixDenote A) h :=
  fun i j => denote_supported A[i][j]

def matrixMulProgram (A : DenseMatrix K D m n a) (B : DenseMatrix K D n r b) :
    Work K (DenseMatrix K D m r (a + b)) :=
  collect m fun i => collect r fun k =>
    Work.bind (collect n fun j => mulProgram A[i][j] B[j][k]) sumProgram

@[simp] theorem matrixMulProgram_cost
    (A : DenseMatrix K D m n a) (B : DenseMatrix K D n r b) :
    (matrixMulProgram A B).cost =
      m * r * n * boxSize D (a + b) * (2 * boxSize D a + 1) := by
  simp only [matrixMulProgram, collect_cost, Work.bind_cost, mulProgram_cost, sumProgram_cost,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
  ring

theorem matrixMulProgram_correct
    (A : DenseMatrix K D m n a) (B : DenseMatrix K D n r b) :
    matrixDenote (matrixMulProgram A B).value = matrixDenote A * matrixDenote B := by
  funext i k
  change denote ((matrixMulProgram A B).value[i][k]) = _
  simp only [matrixMulProgram, collect_value_get, Work.bind_value]
  rw [sumProgram_correct]
  simp only [collect_value_get, mulProgram_correct]
  rfl

def matrixAddProgram (A : DenseMatrix K D m n a) (B : DenseMatrix K D m n b) :
    Work K (DenseMatrix K D m n (max a b)) :=
  collect m fun i => collect n fun j => addProgram A[i][j] B[i][j]

@[simp] theorem matrixAddProgram_cost
    (A : DenseMatrix K D m n a) (B : DenseMatrix K D m n b) :
    (matrixAddProgram A B).cost = m * n * boxSize D (max a b) := by
  simp [matrixAddProgram, mul_assoc]

theorem matrixAddProgram_correct
    (A : DenseMatrix K D m n a) (B : DenseMatrix K D m n b) :
    matrixDenote (matrixAddProgram A B).value = matrixDenote A + matrixDenote B := by
  funext i j
  change denote ((matrixAddProgram A B).value[i][j]) = _
  simp only [matrixAddProgram, collect_value_get, addProgram_correct]
  rfl

end Decoupling.HighDim.LaurentArithmetic
