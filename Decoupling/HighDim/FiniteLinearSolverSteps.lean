import Decoupling.HighDim.FiniteLinearSolverData

/-! # Correctness of the two genuine Gaussian reconstruction steps -/
namespace Decoupling.HighDim.FiniteLinearSolver
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K : Type u} [Field K]

omit [Field K] in
theorem cons_tail {n : ℕ} (x : Fin (n + 1) → K) :
    Fin.cons (x 0) (fun i => x i.succ) = x := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

theorem empty_correct {m : ℕ} (A : DenseMatrix K m 0) (b : Vector K m)
    (hb : ∀ i : Fin m, b[i] = 0) : Correct A b emptySolution where
  dimension_le := by rfl
  sound := by
    intro t
    funext i
    simp [matrix, mulVec, dotProduct, vector, hb]
  complete := by
    intro x _
    exact ⟨Fin.elim0, by funext i; exact Fin.elim0 i⟩
  coordinates := by intro t; funext i; exact Fin.elim0 i

theorem empty_solves_iff {m : ℕ} (A : DenseMatrix K m 0) (b : Vector K m) :
    (∃ x, Solves A b x) ↔ ∀ i : Fin m, b[i] = 0 := by
  constructor
  · rintro ⟨x, hx⟩ i
    have h := congrFun hx i
    simpa [matrix, mulVec, dotProduct, vector] using h.symm
  · intro hb
    exact ⟨emptySolution.realize Fin.elim0, (empty_correct A b hb).sound _⟩

theorem correct_freeExtend {m n : ℕ} (A : DenseMatrix K m (n + 1)) (b : Vector K m)
    (hz : ∀ i : Fin m, A[i][0] = 0) (s : Solution K n) (hs : Correct (tailMatrix A) b s) :
    Correct A b (freeExtend s) where
  dimension_le := Nat.add_le_add_right hs.dimension_le 1
  sound := by
    intro t
    erw [freeExtend_realize]
    exact (solves_tail_iff A b hz _ _).mpr (hs.sound _)
  complete := by
    intro x hx
    have hy : Solves (tailMatrix A) b (fun i => x i.succ) :=
      (solves_tail_iff A b hz (x 0) _).mp (by simpa only [cons_tail] using hx)
    obtain ⟨t, ht⟩ := hs.complete _ hy
    refine ⟨Fin.cons (x 0) t, ?_⟩
    erw [freeExtend_realize]
    simp +instances only [Fin.cons_zero, Fin.cons_succ]
    rw [ht, cons_tail]
  coordinates := by
    intro t
    erw [freeExtend_realize, freeExtend_extract]
    simp only [Fin.cons_zero, Fin.cons_succ, hs.coordinates]
    exact cons_tail t

theorem correct_pivotExtend {m n : ℕ} (A : DenseMatrix K m (n + 1)) (b : Vector K m)
    (r : Fin m) (hp : A[r][0] ≠ 0) (s : Solution K n)
    (hs : Correct (eliminatedMatrix A r) (eliminatedRhs A b r) s) :
    Correct A b (pivotExtend A b r s) where
  dimension_le := hs.dimension_le.trans (Nat.le_succ n)
  sound := by
    intro t
    erw [pivotExtend_realize]
    exact (solves_pivot_iff A b r hp _ _).mpr ⟨rfl, hs.sound t⟩
  complete := by
    intro x hx
    have hy := (solves_pivot_iff A b r hp (x 0) (fun i => x i.succ)).mp
      (by simpa only [cons_tail] using hx)
    obtain ⟨t, ht⟩ := hs.complete _ hy.2
    refine ⟨t, ?_⟩
    rw [pivotExtend_realize, ht, ← hy.1, cons_tail]
  coordinates := by
    intro t
    erw [pivotExtend_realize, pivotExtend_extract]
    simp only [Fin.cons_succ]
    exact hs.coordinates t

end Decoupling.HighDim.FiniteLinearSolver
