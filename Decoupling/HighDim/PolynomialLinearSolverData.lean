import Decoupling.HighDim.PolynomialLinearSolverIndex
import Decoupling.HighDim.EffectiveLinearMatrixEntries

/-!
# Dense polynomial data and its genuine polynomial semantics

The executable representation consists solely of coefficient arrays.
The polynomial denotation and linear equivalences are proof interfaces;
the solver never executes polynomial multiplication or basis choice.
Its coefficient matrix will be assembled by natural-number shifts and
lookups into these arrays.
-/
namespace Decoupling.HighDim.PolynomialLinearSolver
open EffectiveLinear FiniteLinearSolver MvPolynomial
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

universe u
variable {K : Type u} [Field K]

abbrev CoeffVector (K : Type u) (N n b : ℕ) := DenseMatrix K n (boxSize N b)
abbrev CoeffMatrix (K : Type u) (N m n d : ℕ) := DenseMatrix (Vector K (boxSize N d)) m n

def flattenVector {N n b : ℕ} (v : CoeffVector K N n b) : Vector K (n * boxSize N b) :=
  Vector.ofFn fun k =>
    let i := (finProdFinEquiv (m := n) (n := boxSize N b)).symm k
    v[i.1][i.2]

/-- The unique genuine boxed polynomial with the supplied dense coefficients. -/
noncomputable def denotePolynomial (N b : ℕ) (v : Vector K (boxSize N b)) : BoxPolynomial K N b :=
  (boxCoordinates K N b).symm (fun a => v[(boxIndex N b).symm a])

theorem denotePolynomial_coeff (N b : ℕ) (v : Vector K (boxSize N b)) (a : BoxExponent N b) :
    (denotePolynomial N b v).val.coeff a.val = v[(boxIndex N b).symm a] := by
  rw [← boxCoordinates_apply]
  exact congrFun ((boxCoordinates K N b).apply_symm_apply _) a

theorem boxed_coeff_zero {N b : ℕ} (P : BoxPolynomial K N b) (a : Fin N →₀ ℕ)
    (ha : ¬ ∀ i, a i ≤ b) : P.val.coeff a = 0 := by
  by_contra hn
  exact ha ((MvPolynomial.mem_restrictDegree (Fin N) P.val b).mp P.property a
    (MvPolynomial.mem_support_iff.mpr hn))

noncomputable def denoteVector {N n b : ℕ} (v : CoeffVector K N n b) :
    Fin n → BoxPolynomial K N b := fun i => denotePolynomial N b v[i]

noncomputable def denoteMatrix {N m n d : ℕ} (A : CoeffMatrix K N m n d) :
    Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K) :=
  fun i j => (denotePolynomial N d A[i][j]).val

theorem denoteMatrix_degree {N m n d : ℕ} (A : CoeffMatrix K N m n d) :
    ∀ i j, denoteMatrix A i j ∈ MvPolynomial.restrictDegree (Fin N) K d :=
  fun i j => (denotePolynomial N d A[i][j]).property

/-- Flat coefficient coordinates for the actual bounded polynomial vectors. -/
noncomputable def denseCoordinates (N n b : ℕ) :
    (Fin n → BoxPolynomial K N b) ≃ₗ[K] (Fin (n * boxSize N b) → K) where
  toFun y i := vectorCoordinates K N n b y (systemIndex N n b i)
  invFun z := (vectorCoordinates K N n b).symm (fun i => z ((systemIndex N n b).symm i))
  left_inv y := by
    apply (vectorCoordinates K N n b).injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    dsimp only
    rw [Equiv.apply_symm_apply]
  right_inv z := by
    funext i
    dsimp only
    rw [LinearEquiv.apply_symm_apply, Equiv.symm_apply_apply]
  map_add' y z := by
    funext i
    exact congrFun ((vectorCoordinates K N n b).map_add y z) (systemIndex N n b i)
  map_smul' a y := by
    funext i
    exact congrFun ((vectorCoordinates K N n b).map_smul a y) (systemIndex N n b i)

theorem denseCoordinates_denoteVector {N n b : ℕ} (v : CoeffVector K N n b) :
    denseCoordinates (K := K) N n b (denoteVector v) = vector (flattenVector v) := by
  funext k
  change (denotePolynomial N b v[(systemIndex N n b k).1]).val.coeff
    (systemIndex N n b k).2.val = _
  rw [denotePolynomial_coeff]
  simp [systemIndex, flattenVector, vector]

/-- Dense inputs carry their coefficient values explicitly. This lookup
uses only comparisons and subtraction on exponent natural numbers. -/
def shiftedLookup {N d : ℕ} (v : Vector K (boxSize N d))
    (a c : Fin N →₀ ℕ) : K :=
  if h : ∀ i, a i ≤ c i then
    if hd : ∀ i, c i - a i ≤ d then
      v[finFunctionFinEquiv (fun i => (⟨c i - a i, Nat.lt_succ_of_le (hd i)⟩ : Fin (d + 1)))]
    else 0
  else 0

theorem shiftedLookup_eq_coeff {N d : ℕ} (v : Vector K (boxSize N d))
    (a c : Fin N →₀ ℕ) :
    shiftedLookup v a c = if a ≤ c then (denotePolynomial N d v).val.coeff (c - a) else 0 := by
  by_cases h : ∀ i, a i ≤ c i
  · have hac : a ≤ c := h
    simp only [shiftedLookup, dite_eq_left h, ite_eq_left hac]
    by_cases hd : ∀ i, c i - a i ≤ d
    · rw [dite_eq_left hd]
      let e : BoxExponent N d := ⟨c - a, hd⟩
      rw [denotePolynomial_coeff N d v e]
      rfl
    · rw [dite_eq_right hd, boxed_coeff_zero _ _ hd]
  · have hac : ¬ a ≤ c := h
    simp only [shiftedLookup, dite_eq_right h, ite_eq_right hac]

end Decoupling.HighDim.PolynomialLinearSolver
