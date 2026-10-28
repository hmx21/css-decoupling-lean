import Decoupling.HighDim.SparseCircuitSupport

/-! # HD014 actual on-site SWAP count in canonical physical coordinates -/
namespace Decoupling.HighDim.OnSiteSwap
open Circuit SparseCircuit DenseCircuitPermutation LaurentArithmetic ArithmeticCost
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] [DecidableEq K] {D m n a b : ℕ} {ι κ : Type*}

omit [Field K] [DecidableEq K] in
@[simp] theorem count_append (u v : List (Layer K D ι)) :
    swapCount (u ++ v) = swapCount u + swapCount v := by simp [swapCount]

omit [Field K] [DecidableEq K] in
@[simp] theorem count_sum (u : List (SUM K D ι)) :
    swapCount (u.map Layer.sum) = 0 := by simp [swapCount,List.countP_map,isSwap]

omit [Field K] [DecidableEq K] in
@[simp] theorem count_swap (u : List (SWAP ι)) :
    swapCount (u.map (Layer.swap (K := K) (D := D))) = u.length := by
  simp [swapCount,List.countP_map,isSwap]

omit [Field K] [DecidableEq K] in
@[simp] theorem count_relabel (e : ι ≃ κ) (u : List (Layer K D ι)) :
    swapCount (u.map (relabelLayer e)) = swapCount u := by
  simp only [swapCount,List.countP_map]
  congr 1
  funext g
  cases g <;> rfl

omit [DecidableEq K] in
theorem canonical_count (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    swapCount (canonicalThetaProgram f g).value =
      (compileSum n m ((canonicalIdentification m n).symm.trans (Equiv.sumComm _ _))).length := by
  simp only [canonicalThetaProgram,Work.bind_value,Work.pure_value,count_relabel,
    thetaProgramWith,count_append,count_swap,DenseShearCompile.thetaProgram,count_sum,zero_add]

omit [DecidableEq K] in
theorem canonical_count_le (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    swapCount (canonicalThetaProgram f g).value ≤ n+m := by
  rw [canonical_count]
  exact compileSum_length _ _ _

theorem sparse_canonical_count_le (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    swapCount (eraseZeroSUM (canonicalThetaProgram f g).value) ≤ n+m := by
  rw [swapCount_erase]
  exact canonical_count_le f g

omit [Field K] [DecidableEq K] in
theorem swap_sites_same_cell (g : SWAP ι) (cell : Translation D) :
    (g.source cell).2 = cell ∧ (g.destination cell).2 = cell := ⟨rfl,rfl⟩

omit [Field K] [DecidableEq K] in
theorem swap_displacement (g : SWAP ι) :
    (Layer.swap (K := K) (D := D) g).displacement = 0 := rfl

omit [Field K] [DecidableEq K] in
theorem onsite_of_isSwap (g : Layer K D ι) (hg : isSwap g = true) (cell : Translation D) :
    (g.source cell).2 = cell ∧ (g.destination cell).2 = cell := by
  cases g with
  | sum g => simp [isSwap] at hg
  | swap g => exact swap_sites_same_cell g cell

end Decoupling.HighDim.OnSiteSwap
