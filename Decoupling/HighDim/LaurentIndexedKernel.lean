import Decoupling.HighDim.LaurentIndexedSystem

/-! # HD012 actual Laurent kernel generators from the finite-index polynomial solver -/
namespace Decoupling.HighDim.LaurentPresentation
open Matrix MvPolynomial
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [CommRing K] {D m n t : ℕ}

def indexedEvaluation : MvPolynomial (Fin (D + D)) K →+* Laurent K D :=
  (evaluate K D).comp variableEquiv.symm.toRingHom

def indexedProjection (z : Fin (n + m * D) → MvPolynomial (Fin (D + D)) K) :
    Fin n → Laurent K D := projectVector (decodeUnknown z)

theorem indexed_evaluate (A : Matrix (Fin m) (Fin n) (Laurent K D))
    (z : Fin (n + m * D) → MvPolynomial (Fin (D + D)) K) (i : Fin m) :
    indexedEvaluation ((indexedMatrix A *ᵥ z) i) = (A *ᵥ indexedProjection z) i := by
  rw [indexed_mulVec]
  change evaluate K D (variableEquiv.symm (variableEquiv _)) = _
  rw [AlgEquiv.symm_apply_apply]
  exact evaluate_expanded A (decodeUnknown z) i

@[simp] theorem indexedEvaluation_rhs (b : Fin m → Laurent K D) (i : Fin m) :
    indexedEvaluation (indexedRhs b i) = b i := by
  change evaluate K D (variableEquiv.symm (variableEquiv (liftPolynomial D K (b i)))) = b i
  rw [AlgEquiv.symm_apply_apply, evaluate_liftPolynomial]

theorem indexed_lift_solution (A : Matrix (Fin m) (Fin n) (Laurent K D))
    (b : Fin m → Laurent K D) (y : Fin n → Laurent K D) (hy : A *ᵥ y = b) :
    ∃ z, indexedMatrix A *ᵥ z = indexedRhs b ∧ indexedProjection z = y := by
  obtain ⟨z, hz, hp⟩ := lift_solution A b y hy
  refine ⟨encodeUnknown z, (indexed_solution_iff A b _).mpr ?_, ?_⟩
  · simpa using hz
  · simpa [indexedProjection] using hp

def indexedProjectMatrix
    (V : Matrix (Fin (n + m * D)) (Fin t) (MvPolynomial (Fin (D + D)) K)) :
    Matrix (Fin n) (Fin t) (Laurent K D) :=
  fun i j => indexedEvaluation (V (unknownEquiv (Sum.inl i)) j)

theorem indexed_project_mulVec
    (V : Matrix (Fin (n + m * D)) (Fin t) (MvPolynomial (Fin (D + D)) K))
    (z : Fin t → MvPolynomial (Fin (D + D)) K) :
    indexedProjection (V *ᵥ z) =
      indexedProjectMatrix V *ᵥ (fun j => indexedEvaluation (z j)) := by
  funext i
  change indexedEvaluation ((V *ᵥ z) (unknownEquiv (Sum.inl i))) = _
  exact RingHom.map_mulVec indexedEvaluation V z _

/-- The polynomial solver's actual range/kernel equality transports to
the entire Laurent kernel, not merely its bounded coefficient window. -/
theorem indexed_projected_kernel (A : Matrix (Fin m) (Fin n) (Laurent K D))
    (V : Matrix (Fin (n + m * D)) (Fin t) (MvPolynomial (Fin (D + D)) K))
    (hV : V.mulVecLin.range = (indexedMatrix A).mulVecLin.ker) :
    (indexedProjectMatrix V).mulVecLin.range = A.mulVecLin.ker := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    let z : Fin t → MvPolynomial (Fin (D + D)) K :=
      fun j => variableEquiv (liftPolynomial D K (u j))
    have hz : V *ᵥ z ∈ (indexedMatrix A).mulVecLin.ker := by
      rw [← hV]
      exact ⟨z, rfl⟩
    have hp : indexedProjectMatrix V *ᵥ u = indexedProjection (V *ᵥ z) := by
      rw [indexed_project_mulVec]
      congr 1
      funext j
      exact (indexedEvaluation_rhs u j).symm
    change A *ᵥ (indexedProjectMatrix V *ᵥ u) = 0
    rw [hp]
    funext i
    rw [← indexed_evaluate]
    change indexedEvaluation (((indexedMatrix A).mulVecLin (V *ᵥ z)) i) = 0
    change (indexedMatrix A).mulVecLin (V *ᵥ z) = 0 at hz
    rw [hz, Pi.zero_apply, map_zero]
  · intro hy
    obtain ⟨z, hz, hp⟩ := indexed_lift_solution A 0 y hy
    have hz0 : z ∈ (indexedMatrix A).mulVecLin.ker := by
      change indexedMatrix A *ᵥ z = 0
      rw [hz]
      funext i
      simp [indexedRhs, liftVector, liftPolynomial]
    rw [← hV] at hz0
    obtain ⟨u, hu⟩ := hz0
    refine ⟨fun j => indexedEvaluation (u j), ?_⟩
    change indexedProjectMatrix V *ᵥ (fun j => indexedEvaluation (u j)) = y
    rw [← indexed_project_mulVec]
    exact (congrArg indexedProjection hu).trans hp

theorem indexedProjectMatrix_supported
    (V : Matrix (Fin (n + m * D)) (Fin t) (MvPolynomial (Fin (D + D)) K))
    (B : ℕ) (hV : ∀ i j, (V i j).totalDegree ≤ B) :
    LaurentBoxes.MatrixSupported (indexedProjectMatrix V) B := by
  intro i j
  apply evaluate_supported
  change (variableEquiv.symm (V (unknownEquiv (Sum.inl i)) j)).totalDegree ≤ B
  rw [variableEquiv_symm_degree]
  exact hV _ _

end
end Decoupling.HighDim.LaurentPresentation
