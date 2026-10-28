import Decoupling.HighDim.AlgorithmTwoPipelineProperties

/-! # A computed common coefficient radius for the comparison stage -/
namespace Decoupling.HighDim.AlgorithmTwoPipeline
open ArithmeticCost
variable {K : Type} [Field K] [DecidableEq K] {D h : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
variable {cC : StableFree.Coordinates C}
  {b : ∀ j : Fin (D-1), LaurentArithmetic.DenseMatrix K D (cC.rank (j.val+1))
    (cC.rank ((j.val:ℤ)+1-1)) h}
  {d : ∀ j : Fin (D-1), LaurentArithmetic.DenseMatrix K D (cC.rank ((j.val:ℤ)+1+1))
    (cC.rank (j.val+1)) h}

namespace StoredLayers

def commonRadius (s : StoredLayers cC b d) : ℕ := h+1+∑ j : Fin (D-1), s.data[j].radius

theorem input_le_commonRadius (s : StoredLayers cC b d) : h ≤ s.commonRadius := by unfold commonRadius; omega

theorem one_le_commonRadius (s : StoredLayers cC b d) : 1 ≤ s.commonRadius := by unfold commonRadius; omega

theorem radius_le_commonRadius (s : StoredLayers cC b d) (j : Fin (D-1)) :
    LaurentLinearSolver.outputBox D (cC.rank ((j.val:ℤ)+1+1)) h ≤ s.commonRadius := by
  have hj : s.data[j].radius ≤ ∑ j : Fin (D-1), s.data[j].radius :=
    Finset.single_le_sum (f := fun j : Fin (D-1) => s.data[j].radius) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [s.correct j] at hj
  change LaurentLinearSolver.outputBox D (cC.rank ((j.val:ℤ)+1+1)) h ≤ _ at hj
  unfold commonRadius
  omega

theorem commonRadius_bound (s : StoredLayers cC b d) (B : ℕ)
    (hB : ∀ j : Fin (D-1), LaurentLinearSolver.outputBox D (cC.rank ((j.val:ℤ)+1+1)) h ≤ B) :
    s.commonRadius ≤ h+1+(D-1)*B := by
  unfold commonRadius
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _j : Fin (D-1), B := Finset.sum_le_sum fun j _ => by
      rw [s.correct j]
      exact hB j
    _ = _ := by simp

end StoredLayers
end Decoupling.HighDim.AlgorithmTwoPipeline
