import Decoupling.HighDim.FiniteLinearSolverProgram

/-!
# Correctness of the executable Gaussian solver

Pivot existence and nonvanishing are supplied by the actual finite
scan. The result parametrizes all solutions with a computable inverse
given by its stored free columns. Inconsistency is also certified.
-/
namespace Decoupling.HighDim.FiniteLinearSolver
open ArithmeticCost Matrix
universe u
variable {K : Type u} [Field K] [DecidableEq K]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

theorem gaussian_specification : ∀ (n : ℕ) {m : ℕ}
    (A : DenseMatrix K m n) (b : Vector K m), Specification A b (gaussian n A b).value := by
  intro n
  induction n with
  | zero =>
    intro m A b
    simp only [gaussian, Work.bind_value]
    cases hr : (firstNonzero m (vector b)).value with
    | none =>
      exact empty_correct A b ((firstNonzero_none m (vector b)).mp hr)
    | some r =>
      intro h
      exact (firstNonzero_some m (vector b) r hr) ((empty_solves_iff A b).mp h r)
  | succ n ih =>
    intro m A b
    simp only [gaussian, Work.bind_value]
    cases hpiv : (firstNonzero m (fun i => A[i][0])).value with
    | none =>
      have hz := (firstNonzero_none m (fun i => A[i][0])).mp hpiv
      change Specification A b ((gaussian n (tailMatrix A) b).value.map freeExtend)
      have hc := ih (tailMatrix A) b
      cases hs : (gaussian n (tailMatrix A) b).value with
      | none =>
        rw [hs] at hc
        change ¬ ∃ x, Solves A b x
        intro h
        obtain ⟨x, hx⟩ := h
        apply hc
        refine ⟨fun i => x i.succ, ?_⟩
        exact (solves_tail_iff A b hz (x 0) _).mp (by simpa only [cons_tail] using hx)
      | some s =>
        rw [hs] at hc
        change Correct A b (freeExtend s)
        exact correct_freeExtend A b hz s hc
    | some r =>
      have hp := firstNonzero_some m (fun i => A[i][0]) r hpiv
      simp only [Work.bind_value, eliminateProgram_value]
      have hc := ih (eliminatedMatrix A r) (eliminatedRhs A b r)
      cases hs : (gaussian n (eliminatedMatrix A r) (eliminatedRhs A b r)).value with
      | none =>
        rw [hs] at hc
        change ¬ ∃ x, Solves A b x
        intro h
        obtain ⟨x, hx⟩ := h
        apply hc
        refine ⟨fun i => x i.succ, ?_⟩
        exact ((solves_pivot_iff A b r hp (x 0) _).mp
          (by simpa only [cons_tail] using hx)).2
      | some s =>
        rw [hs] at hc
        simpa only [Work.bind_value, Work.pure_value, pivotProgram_value, Specification] using
          correct_pivotExtend A b r hp s hc

theorem gaussian_correct {m n : ℕ} (A : DenseMatrix K m n) (b : Vector K m)
    (s : Solution K n) (h : (gaussian n A b).value = some s) : Correct A b s := by
  have hs := gaussian_specification n A b
  simpa only [h, Specification] using hs

theorem gaussian_none_iff {m n : ℕ} (A : DenseMatrix K m n) (b : Vector K m) :
    (gaussian n A b).value = none ↔ ¬ ∃ x, Solves A b x := by
  constructor
  · intro h
    have hs := gaussian_specification n A b
    simpa only [h, Specification] using hs
  · intro h
    cases hs : (gaussian n A b).value with
    | none => rfl
    | some s => exact False.elim (h ⟨s.realize 0, (gaussian_correct A b s hs).sound 0⟩)

theorem gaussian_some_of_consistent {m n : ℕ} (A : DenseMatrix K m n) (b : Vector K m)
    (h : ∃ x, Solves A b x) : (gaussian n A b).value.isSome := by
  exact Option.ne_none_iff_isSome.mp (fun hn => (gaussian_none_iff A b).mp hn h)

/-- Computably extract the actual solver's successful result. The
consistency proof is erased; no chosen solution is used. -/
def consistentSolution {m n : ℕ} (A : DenseMatrix K m n) (b : Vector K m)
    (h : ∃ x, Solves A b x) : Solution K n :=
  (gaussian n A b).value.get (gaussian_some_of_consistent A b h)

theorem consistentSolution_correct {m n : ℕ} (A : DenseMatrix K m n) (b : Vector K m)
    (h : ∃ x, Solves A b x) : Correct A b (consistentSolution A b h) :=
  gaussian_correct A b _ (Option.some_get _).symm

theorem consistentSolution_particular {m n : ℕ} (A : DenseMatrix K m n) (b : Vector K m)
    (h : ∃ x, Solves A b x) : Solves A b (vector (consistentSolution A b h).particular) := by
  have hs := (consistentSolution_correct A b h).sound 0
  simpa only [Solution.realize, Matrix.mulVec_zero, add_zero] using hs

end Decoupling.HighDim.FiniteLinearSolver
