import Decoupling.HighDim.AlgorithmTwoPipelineInput

/-!
# HD012 pure assembly of the original adjacent differential arrays

Only the original adjacent matrices are supplied. The internal total
matrix copies their coefficients in the explicit degree-first order
and inserts zero blocks. It does not perform a change of basis or any
field operation.
-/
namespace Decoupling.HighDim.AlgorithmTwoOriginalArrays
open ArithmeticCost LaurentArithmetic AlgorithmTwoFiniteComplex

variable {K : Type} {D h length : ℕ}

def blockEntry (rank : ℤ → ℕ) (lo : ℤ)
    (d : ∀ i : Fin length, DenseMatrix K D (rank (lo+i+1)) (rank (lo+i)) h)
    [Zero K] (row col : (i : Fin length) × Fin (rank (lo+i))) : Dense K D h :=
  if he : lo+(row.1 : ℤ) = lo+(col.1 : ℤ)+1 then
    (d col.1)[Fin.cast (congrArg rank he) row.2][col.2]
  else Vector.replicate (boxSize D h) 0

def assemble (rank : ℤ → ℕ) (lo : ℤ)
    (d : ∀ i : Fin length, DenseMatrix K D (rank (lo+i+1)) (rank (lo+i)) h)
    [Zero K] : DenseMatrix K D (totalRank rank lo length) (totalRank rank lo length) h :=
  Vector.ofFn fun r => Vector.ofFn fun c =>
    blockEntry rank lo d
      ((finSigmaFinEquiv (n := fun i : Fin length => rank (lo+i))).symm r)
      ((finSigmaFinEquiv (n := fun i : Fin length => rank (lo+i))).symm c)

def assembleProgram (rank : ℤ → ℕ) (lo : ℤ)
    (d : ∀ i : Fin length, DenseMatrix K D (rank (lo+i+1)) (rank (lo+i)) h)
    [Zero K] : Work K (DenseMatrix K D (totalRank rank lo length) (totalRank rank lo length) h) :=
  Work.pure (assemble rank lo d)

theorem assembleProgram_cost (rank : ℤ → ℕ) (lo : ℤ)
    (d : ∀ i : Fin length, DenseMatrix K D (rank (lo+i+1)) (rank (lo+i)) h)
    [Zero K] : (assembleProgram rank lo d).cost = 0 := rfl

variable [Field K]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem assemble_entry (rank : ℤ → ℕ) (lo : ℤ)
    (d : ∀ i : Fin length, DenseMatrix K D (rank (lo+i+1)) (rank (lo+i)) h)
    (row col : Fin length) (a : Fin (rank (lo+row))) (b : Fin (rank (lo+col))) :
    matrixDenote (assemble rank lo d) (finSigmaFinEquiv ⟨row,a⟩) (finSigmaFinEquiv ⟨col,b⟩) =
      if he : lo+(row : ℤ) = lo+(col : ℤ)+1 then
        matrixDenote (d col) (Fin.cast (congrArg rank he) a) b else 0 := by
  simp only [matrixDenote,assemble,Fin.getElem_fin,Vector.getElem_ofFn,
    Equiv.symm_apply_apply,Fin.eta]
  unfold blockEntry
  split_ifs
  · rfl
  · simp [denote]

end Decoupling.HighDim.AlgorithmTwoOriginalArrays
