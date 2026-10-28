import Decoupling.HighDim.StableFreeHomotopy
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Rank bounds for the Schanuel stabilization

These are bounds on the actual extra free ranks in `homotopyStableEquiv`.
They count only the original finite free terms; they do not count the
unknown rank of a projective complement or a basis computation for it.
This module makes no claim about the cost of solving the lifting systems.
-/

namespace Decoupling.HighDim.StableFree

open Finset

/-- The parity totals together count each input free term exactly once. -/
theorem parityRanks_sum (n : ℕ) (r s : ℕ → ℕ) :
    (parityRanks n r s).1 + (parityRanks n r s).2 =
      ∑ i ∈ range n, (r i + s i) := by
  induction n generalizing r s with
  | zero => rfl
  | succ n ih =>
    simp only [parityRanks]
    rw [sum_range_succ']
    have h := ih (fun i => r (i+1)) (fun i => s (i+1))
    omega

theorem parityRanks_fst_le (n : ℕ) (r s : ℕ → ℕ) :
    (parityRanks n r s).1 ≤ ∑ i ∈ range n, (r i + s i) := by
  have := parityRanks_sum n r s
  omega

theorem parityRanks_snd_le (n : ℕ) (r s : ℕ → ℕ) :
    (parityRanks n r s).2 ≤ ∑ i ∈ range n, (r i + s i) := by
  have := parityRanks_sum n r s
  omega

/-- Uniform input matrix-size bounds give a linear bound in the resolution
length for the sum of the two stabilization ranks. -/
theorem parityRanks_sum_le (n B : ℕ) (r s : ℕ → ℕ)
    (hr : ∀ i < n, r i ≤ B) (hs : ∀ i < n, s i ≤ B) :
    (parityRanks n r s).1 + (parityRanks n r s).2 ≤ n * (2 * B) := by
  rw [parityRanks_sum]
  calc
    _ ≤ ∑ _i ∈ range n, 2 * B := by
      apply sum_le_sum
      intro i hi
      have hri := hr i (mem_range.mp hi)
      have hsi := hs i (mem_range.mp hi)
      omega
    _ = _ := by simp

universe u
variable {R : Type u} [CommRing R]
  {C T : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Exact sum of the two identity-check ranks used in the constructed map. -/
theorem cochainStableRanks_sum (cC : Coordinates C) (cT : Coordinates T) (l : ℕ) :
    (cC.rank 2 + (cochainRanks cC cT l).1) +
      (cC.rank 2 + (cochainRanks cC cT l).2) =
    2 * cC.rank 2 + ∑ i ∈ range (l + 2),
      (cT.rank (1 - (i : ℤ)) + cC.rank (1 - (i : ℤ))) := by
  have h := parityRanks_sum (l + 2)
    (fun i => cT.rank (1 - (i : ℤ))) (fun i => cC.rank (1 - (i : ℤ)))
  change (cC.rank 2 + (parityRanks _ _ _).1) +
    (cC.rank 2 + (parityRanks _ _ _).2) = _
  omega

end Decoupling.HighDim.StableFree
