import Decoupling.HighDim.LaurentPresentationLift
import Mathlib.Data.Matrix.Block

/-!
# HD012 exact conversion of Laurent linear systems to polynomial systems

The additional unknowns multiply the actual inverse relations, one copy
for each equation. Both directions of solution lifting are proved over
the genuine rings. A bound on solutions is not an input to this conversion.
-/
namespace Decoupling.HighDim.LaurentPresentation
open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [CommRing K] {D m n : ℕ}

def liftMatrix (A : Matrix (Fin m) (Fin n) (Laurent K D)) : Matrix (Fin m) (Fin n) (Poly K D) :=
  fun i j => liftPolynomial D K (A i j)

def relationMatrix : Matrix (Fin m) (Fin m × Fin D) (Poly K D) :=
  fun i z => if i = z.1 then relation K D z.2 else 0

def expandedMatrix (A : Matrix (Fin m) (Fin n) (Laurent K D)) :
    Matrix (Fin m) (Fin n ⊕ (Fin m × Fin D)) (Poly K D) :=
  Matrix.fromCols (liftMatrix A) relationMatrix

def liftVector (b : Fin m → Laurent K D) : Fin m → Poly K D := fun i => liftPolynomial D K (b i)

def projectVector (z : (Fin n ⊕ (Fin m × Fin D)) → Poly K D) : Fin n → Laurent K D :=
  fun j => evaluate K D (z (Sum.inl j))

theorem expanded_mulVec (A : Matrix (Fin m) (Fin n) (Laurent K D))
    (z : (Fin n ⊕ (Fin m × Fin D)) → Poly K D) (i : Fin m) :
    (expandedMatrix A *ᵥ z) i =
      (∑ j : Fin n, liftPolynomial D K (A i j) * z (Sum.inl j)) +
        ∑ k : Fin D, relation K D k * z (Sum.inr (i, k)) := by
  classical
  simp [expandedMatrix, Matrix.mulVec, dotProduct, liftMatrix, relationMatrix,
    Fintype.sum_sum_type, Fintype.sum_prod_type]

/-- Evaluation of the expanded polynomial equation recovers exactly the
original Laurent equation. Auxiliary relation columns evaluate to zero. -/
theorem evaluate_expanded (A : Matrix (Fin m) (Fin n) (Laurent K D))
    (z : (Fin n ⊕ (Fin m × Fin D)) → Poly K D) (i : Fin m) :
    evaluate K D ((expandedMatrix A *ᵥ z) i) = (A *ᵥ projectVector z) i := by
  rw [expanded_mulVec]
  simp [projectVector, Matrix.mulVec, dotProduct]

/-- Every particular Laurent solution lifts to a genuine polynomial
solution with exactly the prescribed Laurent coordinates. -/
theorem lift_solution (A : Matrix (Fin m) (Fin n) (Laurent K D)) (b : Fin m → Laurent K D)
    (y : Fin n → Laurent K D) (hy : A *ᵥ y = b) :
    ∃ z : (Fin n ⊕ (Fin m × Fin D)) → Poly K D,
      expandedMatrix A *ᵥ z = liftVector b ∧ projectVector z = y := by
  let v : Fin n → Poly K D := fun j => liftPolynomial D K (y j)
  have hr (i : Fin m) :
      liftPolynomial D K (b i) - ∑ j : Fin n, liftPolynomial D K (A i j) * v j ∈ relationIdeal K D := by
    rw [← kernel_evaluate]
    change evaluate K D _ = 0
    simp only [v, map_sub, map_sum, map_mul, evaluate_liftPolynomial]
    change b i - (A *ᵥ y) i = 0
    rw [hy, sub_self]
  have hu (i : Fin m) : ∃ u : Fin D → Poly K D,
      (∑ k, u k * relation K D k) =
        liftPolynomial D K (b i) - ∑ j, liftPolynomial D K (A i j) * v j :=
    Ideal.mem_span_range_iff_exists_fun.mp (hr i)
  choose u hu using hu
  let z := Sum.elim v (fun z : Fin m × Fin D => u z.1 z.2)
  refine ⟨z, ?_, ?_⟩
  · funext i
    rw [expanded_mulVec]
    change (∑ j, liftPolynomial D K (A i j) * v j) +
      (∑ k, relation K D k * u i k) = liftPolynomial D K (b i)
    simp_rw [mul_comm (relation K D _)]
    rw [hu]
    ring
  · funext j
    exact evaluate_liftPolynomial D K (y j)

theorem polynomial_solution_iff (A : Matrix (Fin m) (Fin n) (Laurent K D))
    (b : Fin m → Laurent K D) :
    (∃ y : Fin n → Laurent K D, A *ᵥ y = b) ↔
      ∃ z : (Fin n ⊕ (Fin m × Fin D)) → Poly K D, expandedMatrix A *ᵥ z = liftVector b := by
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨z, hz, _⟩ := lift_solution A b y hy
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩
    refine ⟨projectVector z, ?_⟩
    funext i
    have he := congrArg (evaluate K D) (congrFun hz i)
    rw [evaluate_expanded] at he
    exact he.trans (evaluate_liftPolynomial D K (b i))

end
end Decoupling.HighDim.LaurentPresentation
