import Decoupling.HighDim.LaurentPresentationKernel
import Mathlib.LinearAlgebra.Matrix.Reindex

/-!
# HD012 sizes of the actual Laurent-to-polynomial conversion

An input exponent box of radius h gives actual polynomial degree at most
`max (2*D*h) 2`. There are precisely `n+m*D` unknowns. A degree-B polynomial
solution evaluates into the actual Laurent box of radius B. Relabelling the
two sets of variables as `Fin (D+D)` preserves total degree.
-/
namespace Decoupling.HighDim.LaurentPresentation
open Matrix MvPolynomial
noncomputable section

variable {K : Type*} [CommRing K] {D m n : ℕ}

theorem relation_degree (i : Fin D) : (relation K D i).totalDegree ≤ 2 := by
  cases subsingleton_or_nontrivial K with
  | inl h =>
    have hz : relation K D i = 0 := Subsingleton.elim _ _
    simp [hz]
  | inr h =>
    unfold relation
    refine (totalDegree_sub _ _).trans ?_
    apply max_le
    · exact (totalDegree_mul _ _).trans (by simp)
    · simp

theorem expandedMatrix_degree (A : Matrix (Fin m) (Fin n) (Laurent K D))
    (h : ℕ) (hA : LaurentBoxes.MatrixSupported A h) :
    ∀ i j, (expandedMatrix A i j).totalDegree ≤ max (2 * D * h) 2 := by
  intro i j
  cases j with
  | inl j => exact (liftPolynomial_degree D K (A i j) h (hA i j)).trans (le_max_left _ _)
  | inr z =>
    change (if i = z.1 then relation K D z.2 else 0).totalDegree ≤ _
    split_ifs
    · exact (relation_degree z.2).trans (le_max_right _ _)
    · simp

theorem liftVector_degree (v : Fin m → Laurent K D)
    (h : ℕ) (hv : ∀ i, LaurentBoxes.Supported (v i) h) :
    ∀ i, (liftVector v i).totalDegree ≤ 2 * D * h :=
  fun i => liftPolynomial_degree D K (v i) h (hv i)

@[simp] theorem expanded_unknown_count :
    Fintype.card (Fin n ⊕ (Fin m × Fin D)) = n + m * D := by simp

theorem exponentMap_mem_box (a : (Fin D ⊕ Fin D) →₀ ℕ) (B : ℕ)
    (ha : a.sum (fun _ n => n) ≤ B) :
    exponentMap D a ∈ LaurentBoxes.box D B := by
  classical
  rw [LaurentBoxes.mem_box]
  intro i
  have hb (j : Fin D ⊕ Fin D) : a j ≤ B := by
    have hj : a j ≤ a.sum (fun _ n => n) := by
      rw [Finsupp.sum_fintype _ _ (by simp)]
      exact Finset.single_le_sum (fun k _ => Nat.zero_le (a k)) (Finset.mem_univ j)
    exact hj.trans ha
  change -(B : ℤ) ≤ (a (Sum.inl i) : ℤ) - a (Sum.inr i) ∧
    (a (Sum.inl i) : ℤ) - a (Sum.inr i) ≤ B
  have hp := hb (Sum.inl i)
  have hn := hb (Sum.inr i)
  omega

/-- Evaluation does not introduce Laurent exponents outside the proved box. -/
theorem evaluate_supported (P : Poly K D) (B : ℕ) (hP : P.totalDegree ≤ B) :
    LaurentBoxes.Supported (evaluate K D P) B := by
  classical
  intro a ha
  change a ∈ (P.coeff.mapDomain (exponentMap D)).support at ha
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support ha)
  exact exponentMap_mem_box s B ((MvPolynomial.le_totalDegree hs).trans hP)

/-- Relabel the genuine positive and negative polynomial variables. -/
def variableEquiv : Poly K D ≃ₐ[K] MvPolynomial (Fin (D + D)) K :=
  MvPolynomial.renameEquiv K finSumFinEquiv

@[simp] theorem variableEquiv_degree (P : Poly K D) :
    (variableEquiv P).totalDegree = P.totalDegree :=
  MvPolynomial.totalDegree_renameEquiv _ _

@[simp] theorem variableEquiv_symm_degree (P : MvPolynomial (Fin (D + D)) K) :
    (variableEquiv.symm P).totalDegree = P.totalDegree := by
  have h := variableEquiv_degree (variableEquiv.symm P)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

end
end Decoupling.HighDim.LaurentPresentation
