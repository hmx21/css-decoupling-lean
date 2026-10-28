import Decoupling.HighDim.OnSiteSwap

/-!
# HD014 recorded zero-test postprocessing

The old circuit is evaluated once. Each SUM weight is tested once using the
existing testZero operation; SWAPs require no test. The full trace grows by
exactly this list of tests. Its subtrace of arithmetic operations is unchanged.
-/
namespace Decoupling.HighDim.SparseCircuit
open Circuit ArithmeticCost LaurentArithmetic DenseCircuitPermutation
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] [DecidableEq K] {D : ℕ} {ι : Type*}

def eraseProgram : List (Layer K D ι) → Work K (List (Layer K D ι))
  | [] => Work.pure []
  | .sum g :: word => Work.bind (ArithmeticCost.testZero g.weight) fun z =>
      Work.bind (eraseProgram word) fun tail => Work.pure (if z then tail else .sum g :: tail)
  | .swap g :: word => Work.bind (eraseProgram word) fun tail => Work.pure (.swap g :: tail)

def zeroTestTrace : List (Layer K D ι) → List (Operation K)
  | [] => []
  | .sum g :: word => .testZero g.weight :: zeroTestTrace word
  | .swap _ :: word => zeroTestTrace word

def arithmeticTrace (trace : List (Operation K)) : List (Operation K) :=
  trace.filter fun op => match op with | .testZero _ => false | _ => true

@[simp] theorem eraseProgram_value (word : List (Layer K D ι)) :
    (eraseProgram word).value = eraseZeroSUM word := by
  induction word with
  | nil => rfl
  | cons g word ih =>
    cases g with
    | sum g =>
      by_cases hz : g.weight = 0 <;> simp [eraseProgram,eraseZeroSUM,keep,hz,ih]
    | swap g => simp [eraseProgram,eraseZeroSUM,keep,ih]

theorem eraseProgram_trace (word : List (Layer K D ι)) :
    (eraseProgram word).trace = zeroTestTrace word := by
  induction word with
  | nil => rfl
  | cons g word ih =>
    cases g <;> simp [eraseProgram,Work.bind,Work.pure,ArithmeticCost.testZero,zeroTestTrace,ih]

omit [Field K] [DecidableEq K] in
theorem zeroTestTrace_length_le (word : List (Layer K D ι)) :
    (zeroTestTrace word).length ≤ word.length := by
  induction word with
  | nil => rfl
  | cons g word ih => cases g <;> simp only [zeroTestTrace,List.length_cons] <;> omega

theorem eraseProgram_cost_le (word : List (Layer K D ι)) :
    (eraseProgram word).cost ≤ word.length := by
  rw [Work.cost,eraseProgram_trace]
  exact zeroTestTrace_length_le word

omit [Field K] [DecidableEq K] in
@[simp] theorem arithmeticTrace_append (a b : List (Operation K)) :
    arithmeticTrace (a ++ b) = arithmeticTrace a ++ arithmeticTrace b := List.filter_append _ _

omit [Field K] [DecidableEq K] in
@[simp] theorem arithmeticTrace_tests (word : List (Layer K D ι)) :
    arithmeticTrace (zeroTestTrace word) = [] := by
  induction word with
  | nil => rfl
  | cons g word ih => cases g <;> simp [zeroTestTrace,arithmeticTrace] at ih ⊢ <;> exact ih

/-- The existing compiler is called once before its actual returned list is filtered. -/
def canonicalProgram {m n a b : ℕ} (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    Work K (List (Layer K D (Fin (n+m)))) :=
  Work.bind (canonicalThetaProgram f g) eraseProgram

variable {m n a b : ℕ}
variable (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b)

@[simp] theorem canonicalProgram_value :
    (canonicalProgram f g).value = eraseZeroSUM (canonicalThetaProgram f g).value := by
  simp only [canonicalProgram,Work.bind_value,eraseProgram_value]

theorem canonicalProgram_trace :
    (canonicalProgram f g).trace = (canonicalThetaProgram f g).trace ++
      zeroTestTrace (canonicalThetaProgram f g).value := by
  simp only [canonicalProgram,Work.bind,eraseProgram_trace]

theorem canonicalProgram_cost :
    (canonicalProgram f g).cost = (canonicalThetaProgram f g).cost +
      (zeroTestTrace (canonicalThetaProgram f g).value).length := by
  simp only [Work.cost,canonicalProgram_trace,List.length_append]

theorem canonicalProgram_arithmeticTrace :
    arithmeticTrace (canonicalProgram f g).trace = arithmeticTrace (canonicalThetaProgram f g).trace := by
  rw [canonicalProgram_trace,arithmeticTrace_append,arithmeticTrace_tests,List.append_nil]

theorem canonicalProgram_length :
    (canonicalProgram f g).value.length ≤ supportSize (matrixDenote f) + supportSize (matrixDenote g) + n+m := by
  rw [canonicalProgram_value]
  exact canonicalTheta_sparse_length f g

theorem canonicalProgram_swaps : swapCount (canonicalProgram f g).value ≤ n+m := by
  rw [canonicalProgram_value]
  exact OnSiteSwap.sparse_canonical_count_le f g

theorem canonicalProgram_wordZ : wordZ (canonicalProgram f g).value = wordZ (canonicalThetaProgram f g).value := by
  rw [canonicalProgram_value,wordZ_erase]

theorem canonicalProgram_wordX : wordX (canonicalProgram f g).value = wordX (canonicalThetaProgram f g).value := by
  rw [canonicalProgram_value,wordX_erase]

end Decoupling.HighDim.SparseCircuit
