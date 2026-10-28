import Decoupling.HighDim.AlgorithmTwoPipelineBackend

/-!
# Public finite-vector input boundary

Every input field coefficient is in an actual stored Vector. Shape proofs
only reconcile dependent dimensions; extracting a block performs index
lookup and copying, never unrecorded field arithmetic. RawInput remains a
convenient semantic family of these stored blocks, not the public runtime
coefficient oracle.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipelineBackend
open ArithmeticCost LaurentArithmetic
variable {K : Type} {D L h : ℕ}

structure MatrixBlock (K : Type) (D h : ℕ) where
  rows : ℕ
  columns : ℕ
  coefficients : DenseMatrix K D rows columns h

def MatrixBlock.read (b : MatrixBlock K D h) (m n : ℕ) (hm : b.rows=m) (hn : b.columns=n) :
    DenseMatrix K D m n h := by
  subst m
  subst n
  exact b.coefficients

structure MaterializedInput (K : Type) (D L h : ℕ) where
  ranks : Vector ℕ (AlgorithmTwoPipeline.inputLength L)
  blocks : Vector (MatrixBlock K D h) (AlgorithmTwoPipeline.inputLength L)
  shape : ∀ i, (blocks.get i).rows = rankAt ranks (-(L:ℤ)+i+1) ∧
    (blocks.get i).columns = rankAt ranks (-(L:ℤ)+i)

def MaterializedInput.toRaw (a : MaterializedInput K D L h) : RawInput K D L h where
  ranks := a.ranks
  differential i := (a.blocks.get i).read _ _ (a.shape i).1 (a.shape i).2

private theorem get_ofFn_entry {α : Type*} {n : ℕ} (f : Fin n → α) (i : Fin n) :
    (Vector.ofFn f).get i = f i := by
  change (Vector.ofFn f)[i.val] = _
  rw [Vector.getElem_ofFn]

def RawInput.materialize (a : RawInput K D L h) : MaterializedInput K D L h where
  ranks := a.ranks
  blocks := Vector.ofFn fun i => ⟨_,_,a.differential i⟩
  shape i := by
    simp only [get_ofFn_entry]
    trivial

theorem RawInput.materialize_toRaw (a : RawInput K D L h) : a.materialize.toRaw = a := by
  cases a with
  | mk ranks d =>
    unfold MaterializedInput.toRaw RawInput.materialize
    congr 1
    funext i
    simp only [get_ofFn_entry]
    rfl

variable [Field K] [DecidableEq K]

/-- Closed public entry: actual finite data, original complex/profile validity
in Prop, and the original dimension-bound relation. -/
def executeMaterialized (a : MaterializedInput K D L h) (valid : Valid a.toRaw) (hDL : D ≤ L) :
    Work K (AlgorithmTwoPipeline.RuntimeOutput K D) := execute a.toRaw valid hDL

theorem executeMaterialized_eq_program (a : MaterializedInput K D L h) (valid : Valid a.toRaw) (hDL : D ≤ L) :
    executeMaterialized a valid hDL = AlgorithmTwo.program (coordinates a.toRaw (Classical.choose valid))
      (originalInput a.toRaw (Classical.choose valid) (Classical.choose_spec valid)) hDL :=
  execute_eq_program a.toRaw valid hDL

end Decoupling.HighDim.AlgorithmTwoPipelineBackend
