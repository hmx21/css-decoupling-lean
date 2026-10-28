import Decoupling.HighDim.AlgorithmTwoOriginalArraysNative
import Decoupling.HighDim.PaperInputSize

/-! # Exact coefficient count of the supplied adjacent arrays -/
namespace Decoupling.HighDim.AlgorithmTwoOriginalArrays
open ArithmeticCost LaurentArithmetic AlgorithmInputSize
variable {K : Type} [Field K] {D h L : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]

/-- The number of stored coefficient slots in the original adjacent
matrices: rows times columns times the common Laurent box cardinality. -/
def coefficientCount : ℕ :=
  ∑ i : Fin (AlgorithmTwoPipeline.inputLength L),
    coords.rank (-(L:ℤ)+i+1)*coords.rank (-(L:ℤ)+i)*boxSize D h

omit [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)] in
theorem coefficientCount_eq_paper :
    coefficientCount (D := D) (h := h) (L := L) coords =
      paperCoefficientCount (D := D) (h := h) (L := L) coords := by
  unfold coefficientCount
  rw [← Finset.sum_mul]
  have he := sum_fin_interval (fun j => coords.rank j*coords.rank (j+1)) L
  rw [show (∑ i : Fin (AlgorithmTwoPipeline.inputLength L),
      coords.rank (-(L:ℤ)+i+1)*coords.rank (-(L:ℤ)+i)) =
      ∑ i : Fin (2*L+1), coords.rank (-(L:ℤ)+i)*coords.rank (-(L:ℤ)+i+1) by
    apply Finset.sum_congr rfl
    intro i _
    exact Nat.mul_comm _ _]
  rw [he]
  rfl

def Input.program (inp : Input (L := L) (h := h) coords) :
    Work K (AlgorithmTwoPipeline.Input (L := L) (h := h) coords) :=
  Work.pure (inp.toPipeline coords)

theorem Input.program_cost (inp : Input (L := L) (h := h) coords) :
    (inp.program coords).cost = 0 := rfl

theorem Input.dense_budget (inp : Input (L := L) (h := h) coords)
    (hD : 0 < D) (hnonzero : 0 < AlgorithmTwoPipeline.inputRank coords L) :
    AlgorithmTwoPipeline.inputRank coords L+h ≤
      (2*(2*L+1)+1)*coefficientCount (D := D) (h := h) (L := L) coords := by
  rw [coefficientCount_eq_paper]
  exact pipeline_dense_budget coords (inp.toPipeline coords) hD hnonzero

end Decoupling.HighDim.AlgorithmTwoOriginalArrays
