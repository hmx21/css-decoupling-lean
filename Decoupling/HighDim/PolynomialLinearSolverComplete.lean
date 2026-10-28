import Decoupling.HighDim.PolynomialLinearSolverKernel
import Decoupling.HighDim.EffectiveLinearCompleteness
import Decoupling.HighDim.HermannEffective

/-!
# Complete executable polynomial solving

The input is a dense coefficient box. Its total degree is bounded by
the number of variables times the box width, proved here. The proved
Hermann cutoff therefore makes the executed finite Gaussian search
complete for arbitrary polynomial solutions. No solution-window or
external solver certificate is an input.
-/
namespace Decoupling.HighDim.PolynomialLinearSolver
open EffectiveLinear FiniteLinearSolver ArithmeticCost Matrix MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u
variable {K : Type u} [Field K]

theorem boxed_totalDegree {N d : ℕ} (P : BoxPolynomial K N d) :
    P.val.totalDegree ≤ N * d := by
  classical
  rw [totalDegree, Finset.sup_le_iff]
  intro a ha
  rw [Finsupp.sum_fintype _ _ (by simp)]
  calc
    ∑ i : Fin N, a i ≤ ∑ _i : Fin N, d :=
      Finset.sum_le_sum (fun i _ => (mem_restrictDegree (Fin N) P.val d).mp P.property a ha i)
    _ = N * d := by simp

def coefficientLookup {N d : ℕ} (v : Vector K (boxSize N d)) (a : Fin N →₀ ℕ) : K :=
  if h : ∀ i, a i ≤ d then v[exponentIndex N d ⟨a, h⟩] else 0

theorem coefficientLookup_eq {N d : ℕ} (v : Vector K (boxSize N d)) (a : Fin N →₀ ℕ) :
    coefficientLookup v a = (denotePolynomial N d v).val.coeff a := by
  unfold coefficientLookup
  split_ifs with h
  · exact (denotePolynomial_coeff N d v ⟨a, h⟩).symm
  · exact (boxed_coeff_zero (denotePolynomial N d v) a h).symm

/-- Enlarge a dense coefficient box by copying existing entries and
writing zeros elsewhere; this executes no field operations. -/
def padCoefficients {N d e : ℕ} (v : Vector K (boxSize N d)) :
    Vector K (boxSize N e) :=
  Vector.ofFn fun k => coefficientLookup v (exponentAt N e k).val

theorem padCoefficients_denote {N d e : ℕ} (hde : d ≤ e)
    (v : Vector K (boxSize N d)) :
    (denotePolynomial N e (padCoefficients v)).val = (denotePolynomial N d v).val := by
  classical
  ext a
  by_cases he : ∀ i, a i ≤ e
  · rw [denotePolynomial_coeff N e (padCoefficients v) ⟨a, he⟩]
    simp only [padCoefficients, Fin.getElem_fin, Vector.getElem_ofFn]
    have heq : exponentAt N e ((boxIndex N e).symm ⟨a, he⟩) = ⟨a, he⟩ :=
      (boxIndex N e).apply_symm_apply _
    rw [coefficientLookup_eq, heq]
  · rw [boxed_coeff_zero _ a he, boxed_coeff_zero _ a (by
      intro hd
      exact he (fun i => (hd i).trans hde))]

def padVector {N n d e : ℕ} (v : CoeffVector K N n d) : CoeffVector K N n e :=
  v.map padCoefficients

theorem padVector_denote {N n d e : ℕ} (hde : d ≤ e) (v : CoeffVector K N n d) (i : Fin n) :
    (denoteVector (padVector (e := e) v) i).val = (denoteVector v i).val := by
  change (denotePolynomial N e ((v.map padCoefficients)[i])).val = _
  simp only [Fin.getElem_fin, Vector.getElem_map]
  exact padCoefficients_denote hde _

/-- Computable degree cutoff derived solely from the dense dimensions. -/
def completeCutoff (N m d : ℕ) : ℕ := (4 * m * (N * d)) ^ (2 ^ N)

variable [DecidableEq K]

def solveComplete (N d : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d)
    (v : CoeffVector K N m d) :
    Work K (Option (Solution K (n * boxSize N (completeCutoff N m d)))) :=
  solveBounded N d (completeCutoff N m d) A (padVector v)

theorem solveComplete_none_iff (N d : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d)
    (v : CoeffVector K N m d) :
    (solveComplete N d A v).value = none ↔
      ¬ ∃ y : Fin n → MvPolynomial (Fin N) K,
        denoteMatrix A *ᵥ y = fun i => (denoteVector v i).val := by
  rw [solveComplete, solveBounded_none_iff]
  apply not_congr
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨fun j => (y j).val, hy.trans ?_⟩
    funext i
    exact padVector_denote (Nat.le_add_right _ _) v i
  · intro h
    obtain ⟨y, hy, hdeg⟩ := Hermann.solution_degree_le (denoteMatrix A)
      (fun i => (denoteVector v i).val)
      (fun i j => boxed_totalDegree (denotePolynomial N d A[i][j]))
      (fun i => boxed_totalDegree (denoteVector v i)) h
    refine ⟨fun j => ⟨y j, mem_box_of_totalDegree_le (hdeg j)⟩, hy.trans ?_⟩
    funext i
    exact (padVector_denote (Nat.le_add_right _ _) v i).symm

theorem solveComplete_sound (N d : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d)
    (v : CoeffVector K N m d) (s : Solution K (n * boxSize N (completeCutoff N m d)))
    (hs : (solveComplete N d A v).value = some s) (t : Fin s.dimension → K) :
    denoteMatrix A *ᵥ
        (fun j => ((denseCoordinates N n (completeCutoff N m d)).symm (s.realize t) j).val) =
      fun i => (denoteVector v i).val := by
  have h := solveBounded_sound N d (completeCutoff N m d) A (padVector v) s hs t
  exact h.trans (funext fun i => padVector_denote (Nat.le_add_right _ _) v i)

theorem solveComplete_cost (N d : ℕ) {m n : ℕ} (A : CoeffMatrix K N m n d)
    (v : CoeffVector K N m d) :
    (solveComplete N d A v).cost ≤
      8 * (m * (d + completeCutoff N m d + 1) ^ N +
        n * (completeCutoff N m d + 1) ^ N + 1) ^ 4 :=
  solveBounded_cost N d (completeCutoff N m d) A (padVector v)

end Decoupling.HighDim.PolynomialLinearSolver
