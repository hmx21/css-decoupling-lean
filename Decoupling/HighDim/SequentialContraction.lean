import Decoupling.HighDim.AlgorithmTwoFiniteComplexCoordinates

/-!
# Descending contraction: exact matrix semantics

HD016, Appendix C4, “Inverting Γ up to homotopy”, and C5, “The lines of
Algorithm 2”.  A step solves only the degree-k equation.  The displayed
matrices use the fixed finite total basis, with explicit zero entries off
that degree; this does not change the paper's original input-size measure.
Exactness below is a statement about the actual differential, not a solver
oracle.  The cone wrapper derives it from the native acyclic cone.
-/
namespace Decoupling.HighDim.SequentialContraction
open Matrix AlgorithmTwoFiniteComplex
variable {R : Type*} [CommRing R] {n : ℕ}
set_option maxHeartbeats 1000000

/-- Every actual cycle is an actual boundary. -/
def Exact (d : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ b : Fin n → R, d *ᵥ b = 0 → ∃ a, d *ᵥ a = b

/-- A proved native contraction discharges exactness; its entries are not
used by the descending program. -/
theorem exact_of_contraction (d : Matrix (Fin n) (Fin n) R)
    (hex : ∃ H, d * H + H * d = 1) : Exact d := by
  rintro b hb
  obtain ⟨H, hH⟩ := hex
  refine ⟨H *ᵥ b, ?_⟩
  have h := congrArg (fun A => A *ᵥ b) hH
  rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hb,
    Matrix.mulVec_zero, add_zero, Matrix.one_mulVec] at h
  exact h

/-- All columns strictly above k already satisfy the contraction equation. -/
def Above (degree : Vector ℤ n) (k : ℤ)
    (d H : Matrix (Fin n) (Fin n) R) : Prop :=
  ∀ i j, k < degree.get j → (d * H + H * d) i j = (1 : Matrix (Fin n) (Fin n) R) i j

/-- The degree-k right side, extended by zero to the fixed total basis. -/
def rhs (degree : Vector ℤ n) (k : ℤ) (d H : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => if degree.get j = k then (1 - H * d) i j else 0

/-- Keep exactly the degree -1 component with source degree k. -/
def component (degree : Vector ℤ n) (k : ℤ) (X : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => if degree.get i = k - 1 ∧ degree.get j = k then X i j else 0

/-- Overwrite the newly solved column block; all other coefficients are copied. -/
def install (degree : Vector ℤ n) (k : ℤ) (H X : Matrix (Fin n) (Fin n) R) :
    Matrix (Fin n) (Fin n) R :=
  fun i j => if degree.get j = k then component degree k X i j else H i j

lemma homogeneous_mul_zero (degree : Vector ℤ n)
    (d H : Matrix (Fin n) (Fin n) R)
    (hd : Homogeneous degree degree 1 d) (hH : Homogeneous degree degree (-1) H)
    (i j : Fin n) (hij : degree.get i ≠ degree.get j) : (H * d) i j = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro a _
  by_cases ha : degree.get a = degree.get j + 1
  · rw [hH i a (by omega), zero_mul]
  · rw [hd a j ha, mul_zero]

lemma rhs_off_degree (degree : Vector ℤ n) (k : ℤ)
    (d H : Matrix (Fin n) (Fin n) R)
    (hd : Homogeneous degree degree 1 d) (hH : Homogeneous degree degree (-1) H)
    (i j : Fin n) (hi : degree.get i ≠ k) : rhs degree k d H i j = 0 := by
  unfold rhs
  split_ifs with hj
  · have hij : i ≠ j := by intro he; subst j; exact hi hj
    simp only [Matrix.sub_apply, Matrix.one_apply, ite_eq_right hij,
      homogeneous_mul_zero degree d H hd hH i j (by omega), sub_self]
  · rfl

/-- The previous equation and d²=0 make the new right side a cycle. -/
theorem rhs_cycle (degree : Vector ℤ n) (k : ℤ)
    (d H : Matrix (Fin n) (Fin n) R) (hd : Homogeneous degree degree 1 d)
    (hsq : d * d = 0) (hprev : Above degree k d H) :
    d * rhs degree k d H = 0 := by
  funext i j
  by_cases hj : degree.get j = k
  · have he : ((d * H + H * d) * d) i j = d i j := by
      calc
        _ = ((1 : Matrix (Fin n) (Fin n) R) * d) i j := by
          rw [Matrix.mul_apply, Matrix.mul_apply]
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : degree.get a = degree.get j + 1
          · rw [hprev i a (by omega)]
          · rw [hd a j ha, mul_zero, mul_zero]
        _ = _ := by rw [Matrix.one_mul]
    have hr : (d * (1 - H * d)) i j = 0 := by
      rw [Matrix.add_mul, Matrix.mul_assoc H d d, hsq, Matrix.mul_zero, add_zero] at he
      rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, Matrix.sub_apply, he, sub_self]
    simpa [Matrix.mul_apply, rhs, hj] using hr
  · simp only [Matrix.mul_apply, rhs, ite_eq_right hj, mul_zero, Finset.sum_const_zero,
      Matrix.zero_apply]

/-- Finite freeness is used columnwise: finitely many genuine cycle lifts
assemble to a matrix solution. Existence only rules out solver failure. -/
theorem rhs_solvable (degree : Vector ℤ n) (k : ℤ)
    (d H : Matrix (Fin n) (Fin n) R) (hd : Homogeneous degree degree 1 d)
    (hsq : d * d = 0) (hex : Exact d) (hprev : Above degree k d H) :
    ∃ X, d * X = rhs degree k d H := by
  classical
  have hc := rhs_cycle degree k d H hd hsq hprev
  have hs : ∀ j : Fin n, ∃ a, d *ᵥ a = fun i => rhs degree k d H i j := by
    intro j
    apply hex
    funext i
    exact congrFun (congrFun hc i) j
  choose a ha using hs
  refine ⟨fun i j => a j i, ?_⟩
  funext i j
  exact congrFun (ha j) i

lemma component_homogeneous (degree : Vector ℤ n) (k : ℤ)
    (X : Matrix (Fin n) (Fin n) R) :
    Homogeneous degree degree (-1) (component degree k X) := by
  intro i j hij
  unfold component
  rw [ite_eq_right (by omega)]

/-- Projection of a solved matrix preserves its degree-k equation. -/
theorem component_equation (degree : Vector ℤ n) (k : ℤ)
    (d H X : Matrix (Fin n) (Fin n) R)
    (hd : Homogeneous degree degree 1 d) (hH : Homogeneous degree degree (-1) H)
    (hX : d * X = rhs degree k d H) :
    d * component degree k X = rhs degree k d H := by
  funext i j
  by_cases hi : degree.get i = k
  · by_cases hj : degree.get j = k
    · calc
        _ = (d * X) i j := by
          rw [Matrix.mul_apply, Matrix.mul_apply]
          apply Finset.sum_congr rfl
          intro a _
          by_cases ha : degree.get a = k - 1
          · simp [component, ha, hj]
          · rw [hd i a (by omega), zero_mul, zero_mul]
        _ = _ := congrFun (congrFun hX i) j
    · simp [Matrix.mul_apply, component, hj, rhs]
  · rw [rhs_off_degree degree k d H hd hH i j hi]
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro a _
    by_cases ha : degree.get a = k - 1 ∧ degree.get j = k
    · rw [hd i a (by omega), zero_mul]
    · rw [component, ite_eq_right ha, mul_zero]

lemma install_homogeneous (degree : Vector ℤ n) (k : ℤ)
    (H X : Matrix (Fin n) (Fin n) R) (hH : Homogeneous degree degree (-1) H) :
    Homogeneous degree degree (-1) (install degree k H X) := by
  intro i j hij
  unfold install
  split_ifs
  · exact component_homogeneous degree k X i j hij
  · exact hH i j hij

lemma install_mul (degree : Vector ℤ n) (k : ℤ)
    (d H X : Matrix (Fin n) (Fin n) R) (hd : Homogeneous degree degree 1 d)
    (i j : Fin n) (hj : k ≤ degree.get j) :
    (install degree k H X * d) i j = (H * d) i j := by
  simp only [Matrix.mul_apply]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : degree.get a = degree.get j + 1
  · simp only [install, ite_eq_right (show degree.get a ≠ k by omega)]
  · rw [hd a j ha, mul_zero, mul_zero]

/-- One solved component extends the contraction law by one complete degree. -/
theorem install_above (degree : Vector ℤ n) (k : ℤ)
    (d H X : Matrix (Fin n) (Fin n) R)
    (hd : Homogeneous degree degree 1 d) (hH : Homogeneous degree degree (-1) H)
    (hprev : Above degree k d H) (hX : d * X = rhs degree k d H) :
    Above degree (k-1) d (install degree k H X) := by
  intro i j hj
  have hj' : k ≤ degree.get j := by omega
  simp only [Matrix.add_apply, install_mul degree k d H X hd i j hj']
  by_cases he : degree.get j = k
  · have hdX : (d * install degree k H X) i j = (d * component degree k X) i j := by
      simp [Matrix.mul_apply, install, he]
    rw [hdX, component_equation degree k d H X hd hH hX]
    simp [rhs, he]
  · have hdH : (d * install degree k H X) i j = (d * H) i j := by
      simp only [Matrix.mul_apply, install, ite_eq_right he]
    rw [hdH]
    exact hprev i j (by omega)

/-- The top initialization is valid even for an empty total basis. -/
theorem zero_above (degree : Vector ℤ n) (top : ℤ)
    (d : Matrix (Fin n) (Fin n) R) (hb : ∀ j, degree.get j ≤ top) :
    Above degree top d 0 := by
  intro i j hj
  exact False.elim (by have := hb j; omega)

/-- Once the lower endpoint has been crossed, all actual columns are proved. -/
theorem equation_of_above (degree : Vector ℤ n) (bottom : ℤ)
    (d H : Matrix (Fin n) (Fin n) R) (hb : ∀ j, bottom < degree.get j)
    (hH : Above degree bottom d H) : d * H + H * d = 1 := by
  funext i j
  exact hH i j (hb j)

end Decoupling.HighDim.SequentialContraction
