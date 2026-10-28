import Decoupling.HighDim.StableFreeResourcePolynomial

/-!
# Global bounds for the actual finite Schanuel recursion

The invariant is the sum of both current retract ranks and every remaining
free-term rank. It is conserved by the actual update. This proves output
radius and total arithmetic cost bounds from the true finite tower length;
neither a stage-count certificate nor intermediate size bounds are inputs.
-/
namespace Decoupling.HighDim.StableFree.Resource
open Effective LaurentArithmetic
variable {K : Type*} {D h₀ length s t : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Simultaneous bounds for the exact numerical recurrences attached to the
materialized output and actual Work trace of the recursive program. -/
theorem recursion_bounds (F : DenseTower K D h₀ length s) (G : DenseTower K D h₀ length t)
    (p q h S : ℕ) (hbudget : F.rankBudget G p q ≤ S)
    (hs : s ≤ S) (ht : t ≤ S) (hh : h ≤ S) :
    F.outputBox G p q h ≤ iteratedBound D length S ∧
      F.costBound G p q h ≤ length*iteratedBound D length S := by
  induction F generalizing t p q h S with
  | zero =>
      cases G
      exact ⟨hh,by simp [DenseTower.costBound]⟩
  | @step length s a A F ih =>
      cases G with
      | step b B G =>
        have ha : a ≤ S := by
          dsimp [DenseTower.rankBudget,DenseTower.rankSum] at hbudget
          omega
        have hb : b ≤ S := by
          dsimp [DenseTower.rankBudget,DenseTower.rankSum] at hbudget
          omega
        have hp : p ≤ S := by
          dsimp [DenseTower.rankBudget,DenseTower.rankSum] at hbudget
          omega
        have hq : q ≤ S := by
          dsimp [DenseTower.rankBudget,DenseTower.rankSum] at hbudget
          omega
        have hnext := nextStageBox_le (D := D) hs ha hb hp hq hh
        have hstep := stage_cost_le (D := D) hs ht ha hb hp hq hh
        have hbudget' : F.rankBudget G (b+q) (a+p) ≤ stepBound D S := by
          rw [DenseTower.rankBudget_step A B F G p q]
          exact hbudget.trans (input_le_stepBound D S)
        have hrec := ih G (b+q) (a+p) (nextStageBox D s a b p q h) (stepBound D S)
          hbudget' (ha.trans (input_le_stepBound D S)) (hb.trans (input_le_stepBound D S)) hnext
        refine ⟨hrec.1,?_⟩
        change _ + F.costBound G (b+q) (a+p) (nextStageBox D s a b p q h) ≤ _
        have hbound : stepBound D S ≤ iteratedBound D length (stepBound D S) :=
          input_le_iteratedBound D length (stepBound D S)
        change _ ≤ (length+1)*iteratedBound D length (stepBound D S)
        nlinarith [hrec.2]

/-- For fixed D and a fixed actual tower length, the radius is bounded by
one explicit polynomial in the original rank/radius budget. -/
theorem recursion_output_polynomial (F : DenseTower K D h₀ length s)
    (G : DenseTower K D h₀ length t) (p q h S : ℕ)
    (hbudget : F.rankBudget G p q ≤ S) (hs : s ≤ S) (ht : t ≤ S) (hh : h ≤ S) :
    F.outputBox G p q h ≤ (iteratedPolynomial D length).eval S := by
  rw [iteratedPolynomial_eval]
  exact (recursion_bounds F G p q h S hbudget hs ht hh).1

theorem recursion_cost_polynomial (F : DenseTower K D h₀ length s)
    (G : DenseTower K D h₀ length t) (p q h S : ℕ)
    (hbudget : F.rankBudget G p q ≤ S) (hs : s ≤ S) (ht : t ≤ S) (hh : h ≤ S) :
    F.costBound G p q h ≤ (costPolynomial D length).eval S := by
  rw [costPolynomial_eval]
  exact (recursion_bounds F G p q h S hbudget hs ht hh).2

variable [Field K] [DecidableEq K]

/-- Bound the actual recorded arithmetic, with the semantic validity used
only by the existing correctness proof of the real solver calls. -/
theorem stabilizeProgram_cost_polynomial (F : DenseTower K D h₀ length s)
    (G : DenseTower K D h₀ length t) {p q h : ℕ} (data : EmbeddedArrays K D s t p q h)
    (hh₀ : h₀ ≤ h) (hv : StateValid F G data) (S : ℕ)
    (hbudget : F.rankBudget G p q ≤ S) (hs : s ≤ S) (ht : t ≤ S) (hh : h ≤ S) :
    (stabilizeProgram F G data hh₀ hv).cost ≤ (costPolynomial D length).eval S :=
  (stabilizeProgram_cost F G data hh₀ hv).trans
    (recursion_cost_polynomial F G p q h S hbudget hs ht hh)

end Decoupling.HighDim.StableFree.Resource
