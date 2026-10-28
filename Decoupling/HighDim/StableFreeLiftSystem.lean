import Decoupling.HighDim.StableFreeProjectiveMatrix
import Mathlib.Algebra.MvPolynomial.CommRing

/-!
# Actual finite scalar equations for projective lifts into a presented target

Unknown matrices X and W satisfy `A X - B = D W`, `E X = X`, and
`X G = X`. These are encoded by an explicit scalar coefficient matrix,
not by an assumed matrix-solver oracle. The relations D allow the common
target to be a quotient instead of incorrectly assuming it is projective.
-/

namespace Decoupling.HighDim.StableFree.Effective

open Matrix
noncomputable section
variable {R : Type*} [CommRing R] {v h k l : ℕ}

abbrev LiftRows (v k l : ℕ) := (Fin v ⊕ (Fin k ⊕ Fin k)) × Fin l
abbrev LiftUnknowns (k h l : ℕ) := (Fin k ⊕ Fin h) × Fin l

/-- Unknowns are exactly the entries of the lift X and relation witness W. -/
def liftVector (X : Matrix (Fin k) (Fin l) R) (W : Matrix (Fin h) (Fin l) R) :
    LiftUnknowns k h l → R := fun ij =>
  Sum.elim (fun i => X i ij.2) (fun i => W i ij.2) ij.1

def liftStack (B : Matrix (Fin v) (Fin l) R)
    (C D : Matrix (Fin k) (Fin l) R) : LiftRows v k l → R := fun ij =>
  Sum.elim (fun i => B i ij.2)
    (Sum.elim (fun i => C i ij.2) (fun i => D i ij.2)) ij.1

/-- Each coefficient is a known matrix entry, its negative, or its difference
with an identity entry. No product of unknown entries occurs. -/
def liftCoefficients (A : Matrix (Fin v) (Fin k) R) (D : Matrix (Fin v) (Fin h) R)
    (E : Matrix (Fin k) (Fin k) R) (G : Matrix (Fin l) (Fin l) R) :
    Matrix (LiftRows v k l) (LiftUnknowns k h l) R := fun ij ab =>
  match ij.1, ab.1 with
  | .inl i, .inl a => if ab.2 = ij.2 then A i a else 0
  | .inl i, .inr a => if ab.2 = ij.2 then -D i a else 0
  | .inr (.inl i), .inl a => if ab.2 = ij.2 then (E-1) i a else 0
  | .inr (.inl _), .inr _ => 0
  | .inr (.inr i), .inl a => if a=i then (G-1) ab.2 ij.2 else 0
  | .inr (.inr _), .inr _ => 0

/-- The scalar system is exactly the three original matrix expressions. -/
theorem liftCoefficients_mulVec
    (A : Matrix (Fin v) (Fin k) R) (D : Matrix (Fin v) (Fin h) R)
    (E : Matrix (Fin k) (Fin k) R) (G : Matrix (Fin l) (Fin l) R)
    (X : Matrix (Fin k) (Fin l) R) (W : Matrix (Fin h) (Fin l) R) :
    liftCoefficients A D E G *ᵥ liftVector X W =
      liftStack (A*X-D*W) ((E-1)*X) (X*(G-1)) := by
  classical
  funext ij
  rcases ij with ⟨i|i|i,j⟩ <;>
    simp [liftCoefficients, liftVector, liftStack, Matrix.mulVec, dotProduct,
      Fintype.sum_prod_type, Fintype.sum_sum_type, Matrix.mul_apply, sub_eq_add_neg,
      mul_comm, Finset.sum_neg_distrib]

/-- Exact correspondence of a scalar-system solution and the desired lift
and both projector equations. -/
theorem liftEquation_iff
    (A : Matrix (Fin v) (Fin k) R) (B : Matrix (Fin v) (Fin l) R)
    (D : Matrix (Fin v) (Fin h) R) (E : Matrix (Fin k) (Fin k) R)
    (G : Matrix (Fin l) (Fin l) R)
    (X : Matrix (Fin k) (Fin l) R) (W : Matrix (Fin h) (Fin l) R) :
    liftCoefficients A D E G *ᵥ liftVector X W = liftStack B 0 0 ↔
      A*X-B=D*W ∧ E*X=X ∧ X*G=X := by
  rw [liftCoefficients_mulVec]
  constructor
  · intro hx
    have h₁ : A*X-D*W=B := by
      funext i j
      exact congrFun hx (.inl i,j)
    have h₂ : (E-1)*X=0 := by
      funext i j
      exact congrFun hx (.inr (.inl i),j)
    have h₃ : X*(G-1)=0 := by
      funext i j
      exact congrFun hx (.inr (.inr i),j)
    refine ⟨?_, ?_, ?_⟩
    · rw [← h₁]
      abel
    · rw [Matrix.sub_mul, Matrix.one_mul] at h₂
      exact sub_eq_zero.mp h₂
    · rw [Matrix.mul_sub, Matrix.mul_one] at h₃
      exact sub_eq_zero.mp h₃
  · rintro ⟨h₁,h₂,h₃⟩
    have h₁' : A*X-D*W=B := by rw [←h₁]; abel
    rw [h₁', Matrix.sub_mul, Matrix.one_mul, h₂, sub_self,
      Matrix.mul_sub, Matrix.mul_one, h₃, sub_self]

/-- Any scalar vector decodes to actual matrices of the displayed sizes. -/
theorem liftSolvable_iff
    (A : Matrix (Fin v) (Fin k) R) (B : Matrix (Fin v) (Fin l) R)
    (D : Matrix (Fin v) (Fin h) R) (E : Matrix (Fin k) (Fin k) R)
    (G : Matrix (Fin l) (Fin l) R) :
    (∃ z : LiftUnknowns k h l → R, liftCoefficients A D E G *ᵥ z = liftStack B 0 0) ↔
      ∃ X : Matrix (Fin k) (Fin l) R, ∃ W : Matrix (Fin h) (Fin l) R,
        A*X-B=D*W ∧ E*X=X ∧ X*G=X := by
  constructor
  · rintro ⟨z,hz⟩
    let X : Matrix (Fin k) (Fin l) R := fun i j => z (.inl i,j)
    let W : Matrix (Fin h) (Fin l) R := fun i j => z (.inr i,j)
    have he : liftVector X W = z := by
      funext ij
      rcases ij with ⟨i|i,j⟩ <;> rfl
    exact ⟨X,W,(liftEquation_iff A B D E G X W).mp (by rwa [he])⟩
  · rintro ⟨X,W,hX⟩
    exact ⟨liftVector X W,(liftEquation_iff A B D E G X W).mpr hX⟩

@[simp] theorem card_liftRows : Fintype.card (LiftRows v k l) = (v+2*k)*l := by
  simp [LiftRows, two_mul]

@[simp] theorem card_liftUnknowns : Fintype.card (LiftUnknowns k h l) = (k+h)*l := by
  simp [LiftUnknowns]

section PolynomialDegrees
open MvPolynomial
variable {K : Type*} [CommRing K] {N d : ℕ}

private theorem identity_entry_totalDegree (i j : Fin k) :
    ((1 : Matrix (Fin k) (Fin k) (MvPolynomial (Fin N) K)) i j).totalDegree = 0 := by
  classical
  by_cases h : i=j
  · subst j
    simp only [Matrix.one_apply_eq, totalDegree_one]
  · simp only [Matrix.one_apply_ne h, totalDegree_zero]

/-- The scalar equations do not enlarge the known polynomial coefficient degree. -/
theorem liftCoefficients_totalDegree_le
    (A : Matrix (Fin v) (Fin k) (MvPolynomial (Fin N) K))
    (D : Matrix (Fin v) (Fin h) (MvPolynomial (Fin N) K))
    (E : Matrix (Fin k) (Fin k) (MvPolynomial (Fin N) K))
    (G : Matrix (Fin l) (Fin l) (MvPolynomial (Fin N) K))
    (hA : ∀ i j, (A i j).totalDegree ≤ d) (hD : ∀ i j, (D i j).totalDegree ≤ d)
    (hE : ∀ i j, (E i j).totalDegree ≤ d) (hG : ∀ i j, (G i j).totalDegree ≤ d)
    (ij : LiftRows v k l) (ab : LiftUnknowns k h l) :
    (liftCoefficients A D E G ij ab).totalDegree ≤ d := by
  classical
  rcases ij with ⟨i|i|i,j⟩ <;> rcases ab with ⟨a|a,b⟩
  · dsimp [liftCoefficients]
    split
    · exact hA i a
    · simp
  · dsimp [liftCoefficients]
    split
    · rw [totalDegree_neg]
      exact hD i a
    · simp
  · dsimp [liftCoefficients]
    split
    · exact (totalDegree_sub _ _).trans
        (max_le (hE i a) (by rw [identity_entry_totalDegree]; exact Nat.zero_le d))
    · simp
  · simp [liftCoefficients]
  · dsimp [liftCoefficients]
    split
    · exact (totalDegree_sub _ _).trans
        (max_le (hG b j) (by rw [identity_entry_totalDegree]; exact Nat.zero_le d))
    · simp
  · simp [liftCoefficients]

end PolynomialDegrees
end
end Decoupling.HighDim.StableFree.Effective
