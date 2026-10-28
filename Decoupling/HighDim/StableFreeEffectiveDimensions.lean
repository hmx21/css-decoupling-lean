import Decoupling.HighDim.StableFreeEffectiveFullProgram

/-!
# Proven recursive stage count and uniform matrix sizes

After the initial quotient stage, each base ambient rank is bounded by the
opposite enlarged retract rank. The sum of both retract ranks and all
remaining free ranks is conserved. Consequently every actual scalar solve
has at most 3R² equations and R² unknowns, independent of recursive level.
-/
namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic ArithmeticCost
variable {K : Type*} [Field K] [DecidableEq K] {D h₀ length s t : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace DenseTower

def rankBudget (F : DenseTower K D h₀ length s) (G : DenseTower K D h₀ length t) (p q : ℕ) : ℕ :=
  p+q+F.rankSum+G.rankSum

omit [Field K] [DecidableEq K] in
theorem rankBudget_step {a b : ℕ} (A : DenseMatrix K D s a h₀) (B : DenseMatrix K D t b h₀)
    (F : DenseTower K D h₀ length a) (G : DenseTower K D h₀ length b) (p q : ℕ) :
    rankBudget F G (b+q) (a+p) = rankBudget (.step a A F) (.step b B G) p q := by
  exact budget_step A B F G p q

end DenseTower

/-- Every recorded call corresponds to the concrete compiler dimensions at
its callsite, and every such call obeys the conserved uniform budget. -/
theorem stabilizeProgram_system_dimensions (F : DenseTower K D h₀ length s)
    (G : DenseTower K D h₀ length t) {p q h : ℕ} (data : EmbeddedArrays K D s t p q h)
    (hh : h₀ ≤ h) (hv : StateValid F G data) (hs : s ≤ q) (ht : t ≤ p) :
    ∀ x ∈ (stabilizeProgram F G data hh hv).value.solverSystems,
      x.1 ≤ 3*(F.rankBudget G p q)^2 ∧ x.2.1 ≤ (F.rankBudget G p q)^2 := by
  induction F generalizing t p q h with
  | zero => cases G; simp [stabilizeProgram]
  | @step length s a A F ih =>
    cases G with
    | step b B G =>
      intro x hx
      simp only [stabilizeProgram,Work.bind_value,Work.pure_value,List.mem_cons] at hx
      let budget := (DenseTower.step a A F).rankBudget (.step b B G) p q
      have hvb : s+p ≤ budget := by dsimp [budget,DenseTower.rankBudget,DenseTower.rankSum]; omega
      have hkb : a+p ≤ budget := by dsimp [budget,DenseTower.rankBudget,DenseTower.rankSum]; omega
      have hlb : b+q ≤ budget := by dsimp [budget,DenseTower.rankBudget,DenseTower.rankSum]; omega
      have hrows (k l : ℕ) (hk : k ≤ budget) (hl : l ≤ budget) :
          (s+p+(k+k))*l ≤ 3*budget^2 := by
        have hm := Nat.mul_le_mul (show s+p+(k+k) ≤ 3*budget by omega) hl
        nlinarith
      have hcols (k l : ℕ) (hk : k ≤ budget) (hl : l ≤ budget) : k*l ≤ budget^2 := by
        have hm := Nat.mul_le_mul hk hl
        nlinarith
      rcases hx with rfl|rfl|hx
      · exact ⟨hrows _ _ hkb hlb,hcols _ _ hkb hlb⟩
      · exact ⟨hrows _ _ hlb hkb,hcols _ _ hlb hkb⟩
      · have hi := ih G
          (updateStage data
            (solveStage (prepareStage A B data).value (prepareStage_solvable A B F G data hh hv)).value.1
            (solveStage (prepareStage A B data).value (prepareStage_solvable A B F G data hh hv)).value.2).value
          (hh.trans (Nat.le_max_left _ _)) (updateStage_valid A B F G data hh hv _)
          (by omega) (by omega) x hx
        rw [DenseTower.rankBudget_step A B F G p q] at hi
        exact hi

end Decoupling.HighDim.StableFree.Effective
