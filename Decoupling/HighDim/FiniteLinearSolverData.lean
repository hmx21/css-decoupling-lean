import Decoupling.HighDim.ArithmeticCost
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Dense systems and the semantics of Gaussian solution data

All executable matrix and vector values use finite arrays. The pure
constructors in this file specify the mathematical meaning of the
counted programs; they are not asserted to be those programs' cost.
-/
namespace Decoupling.HighDim.FiniteLinearSolver
open Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u
variable {K : Type u} [Field K]

abbrev DenseMatrix (K : Type u) (m n : ℕ) := Vector (Vector K n) m

def vector {n : ℕ} (v : Vector K n) : Fin n → K := fun i => v[i]
def matrix {m n : ℕ} (A : DenseMatrix K m n) : Matrix (Fin m) (Fin n) K := fun i j => A[i][j]

structure Solution (K : Type u) (n : ℕ) where
  dimension : ℕ
  particular : Vector K n
  kernel : DenseMatrix K n dimension
  freeColumns : Vector (Fin n) dimension

def Solution.realize {n : ℕ} (s : Solution K n) (t : Fin s.dimension → K) : Fin n → K :=
  vector s.particular + matrix s.kernel *ᵥ t

def Solution.extract {n : ℕ} (s : Solution K n) (x : Fin n → K) : Fin s.dimension → K :=
  fun j => x s.freeColumns[j]

def Solves {m n : ℕ} (A : DenseMatrix K m n) (b : Vector K m) (x : Fin n → K) : Prop :=
  matrix A *ᵥ x = vector b

structure Correct {m n : ℕ} (A : DenseMatrix K m n) (b : Vector K m) (s : Solution K n) : Prop where
  dimension_le : s.dimension ≤ n
  sound : ∀ t, Solves A b (s.realize t)
  complete : ∀ x, Solves A b x → ∃ t, s.realize t = x
  coordinates : ∀ t, s.extract (s.realize t) = t

theorem Correct.injective {m n : ℕ} {A : DenseMatrix K m n} {b : Vector K m}
    {s : Solution K n} (h : Correct A b s) : Function.Injective s.realize := by
  intro t u he
  have ht := congrArg s.extract he
  simpa only [h.coordinates] using ht

def Specification {m n : ℕ} (A : DenseMatrix K m n) (b : Vector K m)
    (r : Option (Solution K n)) : Prop :=
  match r with
  | none => ¬ ∃ x, Solves A b x
  | some s => Correct A b s

def emptySolution : Solution K 0 where
  dimension := 0
  particular := #v[]
  kernel := #v[]
  freeColumns := #v[]

def tailMatrix {m n : ℕ} (A : DenseMatrix K m (n + 1)) : DenseMatrix K m n :=
  Vector.ofFn fun i => Vector.ofFn fun j => A[i][j.succ]

def eliminatedMatrix {m n : ℕ} (A : DenseMatrix K m (n + 1)) (r : Fin m) : DenseMatrix K m n :=
  Vector.ofFn fun i => Vector.ofFn fun j => A[i][j.succ] - (A[i][0] / A[r][0]) * A[r][j.succ]

def eliminatedRhs {m n : ℕ} (A : DenseMatrix K m (n + 1)) (b : Vector K m) (r : Fin m) : Vector K m :=
  Vector.ofFn fun i => b[i] - (A[i][0] / A[r][0]) * b[r]

def pivotHead {m n : ℕ} (A : DenseMatrix K m (n + 1)) (b : Vector K m)
    (r : Fin m) (y : Fin n → K) : K :=
  (b[r] - ∑ j : Fin n, A[r][j.succ] * y j) / A[r][0]

def freeExtend {n : ℕ} (s : Solution K n) : Solution K (n + 1) where
  dimension := s.dimension + 1
  particular := ArithmeticCost.prepend 0 s.particular
  kernel := Vector.ofFn (Fin.cases
    (Vector.ofFn (Fin.cases 1 (fun _ => 0)))
    (fun i => Vector.ofFn (Fin.cases 0 (fun j => s.kernel[i][j]))))
  freeColumns := ArithmeticCost.prepend 0 (s.freeColumns.map Fin.succ)

def pivotExtend {m n : ℕ} (A : DenseMatrix K m (n + 1)) (b : Vector K m)
    (r : Fin m) (s : Solution K n) : Solution K (n + 1) where
  dimension := s.dimension
  particular := ArithmeticCost.prepend (pivotHead A b r (vector s.particular)) s.particular
  kernel := ArithmeticCost.prepend
    (Vector.ofFn fun j => -(∑ i : Fin n, A[r][i.succ] * s.kernel[i][j]) / A[r][0]) s.kernel
  freeColumns := s.freeColumns.map Fin.succ

@[simp] theorem freeExtend_extract {n : ℕ} (s : Solution K n) (x : Fin (n + 1) → K) :
    (freeExtend s).extract x = Fin.cons (x 0) (s.extract (fun i => x i.succ)) := by
  funext j
  refine Fin.cases ?_ (fun j => ?_) j
  · change x (ArithmeticCost.prepend 0 (s.freeColumns.map Fin.succ))[0] = x 0
    rw [ArithmeticCost.prepend_zero]
  · change x (ArithmeticCost.prepend 0 (s.freeColumns.map Fin.succ))[j.succ] = _
    rw [ArithmeticCost.prepend_succ]
    change x ((s.freeColumns.map Fin.succ)[j.val]) = _
    rw [Vector.getElem_map]
    rfl

@[simp] theorem pivotExtend_extract {m n : ℕ} (A : DenseMatrix K m (n + 1)) (b : Vector K m)
    (r : Fin m) (s : Solution K n) (x : Fin (n + 1) → K) :
    (pivotExtend A b r s).extract x = s.extract (fun i => x i.succ) := by
  funext j
  change x ((s.freeColumns.map Fin.succ)[j.val]) = _
  rw [Vector.getElem_map]
  rfl

@[simp] theorem freeExtend_realize {n : ℕ} (s : Solution K n) (t : Fin (s.dimension + 1) → K) :
    (freeExtend s).realize t = Fin.cons (t 0) (s.realize (fun j => t j.succ)) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · simp [Solution.realize, freeExtend, vector, matrix, mulVec, dotProduct, Fin.sum_univ_succ,
      ArithmeticCost.prepend]
  · simp [Solution.realize, freeExtend, vector, matrix, mulVec, dotProduct, Fin.sum_univ_succ,
      ArithmeticCost.prepend]

theorem pivotExtend_realize {m n : ℕ} (A : DenseMatrix K m (n + 1)) (b : Vector K m)
    (r : Fin m) (s : Solution K n) (t : Fin s.dimension → K) :
    (pivotExtend A b r s).realize t = Fin.cons (pivotHead A b r (s.realize t)) (s.realize t) := by
  funext i
  refine Fin.cases ?_ (fun i => ?_) i
  · change (pivotExtend A b r s).particular[0] +
      (∑ j : Fin s.dimension, (pivotExtend A b r s).kernel[0][j] * t j) = pivotHead A b r (s.realize t)
    dsimp +instances only [pivotExtend]
    erw [ArithmeticCost.prepend_zero, ArithmeticCost.prepend_zero]
    simp +instances only [Fin.getElem_fin, Vector.getElem_ofFn]
    change pivotHead A b r (vector s.particular) +
      (∑ j : Fin s.dimension, (-(∑ i : Fin n, A[r][i.succ] * s.kernel[i][j]) / A[r][0]) * t j) = _
    have hsum : (∑ j : Fin s.dimension,
        (-(∑ i : Fin n, A[r][i.succ] * s.kernel[i][j]) / A[r][0]) * t j) =
        -(∑ i : Fin n, A[r][i.succ] * (∑ j : Fin s.dimension, s.kernel[i][j] * t j)) / A[r][0] := by
      simp only [div_eq_mul_inv, neg_mul, Finset.sum_neg_distrib,
        Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum]
    simp only [pivotHead, Solution.realize, Pi.add_apply, vector, matrix, mulVec, dotProduct,
      mul_add, Finset.sum_add_distrib, div_eq_mul_inv]
    ring
  · simp [Solution.realize, pivotExtend, vector, matrix, mulVec, dotProduct,
      ArithmeticCost.prepend]

theorem solves_tail_iff {m n : ℕ} (A : DenseMatrix K m (n + 1)) (b : Vector K m)
    (h : ∀ i : Fin m, A[i][0] = 0) (x : K) (y : Fin n → K) :
    Solves A b (Fin.cons x y) ↔ Solves (tailMatrix A) b y := by
  have he : matrix A *ᵥ Fin.cons x y = matrix (tailMatrix A) *ᵥ y := by
    funext i
    simp [matrix, mulVec, dotProduct, Fin.sum_univ_succ, tailMatrix]
    exact Or.inl (h i)
  change matrix A *ᵥ Fin.cons x y = vector b ↔ matrix (tailMatrix A) *ᵥ y = vector b
  rw [he]

/-- Gaussian elimination preserves exactly the solution set, and the
pivot coordinate is uniquely reconstructed from the remaining ones. -/
theorem solves_pivot_iff {m n : ℕ} (A : DenseMatrix K m (n + 1)) (b : Vector K m)
    (r : Fin m) (hp : A[r][0] ≠ 0) (x : K) (y : Fin n → K) :
    Solves A b (Fin.cons x y) ↔
      x = pivotHead A b r y ∧ Solves (eliminatedMatrix A r) (eliminatedRhs A b r) y := by
  have hfull (u : K) (i : Fin m) : (matrix A *ᵥ Fin.cons u y) i =
      A[i][0] * u + ∑ j : Fin n, A[i][j.succ] * y j := by
    simp [matrix, mulVec, dotProduct, Fin.sum_univ_succ]
  have hred (i : Fin m) : (matrix (eliminatedMatrix A r) *ᵥ y) i =
      ∑ j : Fin n, (A[i][j.succ] - (A[i][0] / A[r][0]) * A[r][j.succ]) * y j := by
    simp [matrix, eliminatedMatrix, mulVec, dotProduct]
  have hrow (i : Fin m) :
      ∑ j : Fin n, (A[i][j.succ] - (A[i][0] / A[r][0]) * A[r][j.succ]) * y j =
        (∑ j : Fin n, A[i][j.succ] * y j) -
          (A[i][0] / A[r][0]) * (∑ j : Fin n, A[r][j.succ] * y j) := by
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
  have hid (i : Fin m) :
      A[i][0] * pivotHead A b r y + (∑ j : Fin n, A[i][j.succ] * y j) =
        ((∑ j : Fin n, A[i][j.succ] * y j) -
          (A[i][0] / A[r][0]) * (∑ j : Fin n, A[r][j.succ] * y j)) +
            (A[i][0] / A[r][0]) * b[r] := by unfold pivotHead; ring
  constructor
  · intro h
    have hx : x = pivotHead A b r y := by
      apply (eq_div_iff hp).mpr
      apply (eq_sub_iff_add_eq).mpr
      have hr := congrFun h r
      rw [hfull] at hr
      simpa only [vector, mul_comm] using hr
    refine ⟨hx, ?_⟩
    funext i
    rw [hred, hrow]
    dsimp only [vector, eliminatedRhs]
    simp only [Fin.getElem_fin, Vector.getElem_ofFn]
    rw [eq_sub_iff_add_eq]
    erw [← hid i, ← hx]
    have hi := congrFun h i
    rw [hfull] at hi
    exact hi
  · rintro ⟨rfl, h⟩
    funext i
    rw [hfull, hid]
    have hi := congrFun h i
    rw [hred, hrow] at hi
    dsimp only [vector, eliminatedRhs] at hi
    simp only [Fin.getElem_fin, Vector.getElem_ofFn] at hi
    exact (eq_sub_iff_add_eq).mp hi

end Decoupling.HighDim.FiniteLinearSolver
