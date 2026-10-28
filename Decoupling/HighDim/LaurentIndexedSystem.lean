import Decoupling.HighDim.LaurentPresentationBounds

/-! # HD012 finite-coordinate interface for the actual polynomial presentation -/
namespace Decoupling.HighDim.LaurentPresentation
open Matrix MvPolynomial
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [CommRing K] {D m n : ℕ}

def unknownEquiv : (Fin n ⊕ (Fin m × Fin D)) ≃ Fin (n + m * D) :=
  (Equiv.sumCongr (Equiv.refl _) finProdFinEquiv).trans finSumFinEquiv

def indexedMatrix (A : Matrix (Fin m) (Fin n) (Laurent K D)) :
    Matrix (Fin m) (Fin (n + m * D)) (MvPolynomial (Fin (D + D)) K) :=
  ((expandedMatrix A).map variableEquiv).submatrix id unknownEquiv.symm

def indexedRhs (b : Fin m → Laurent K D) : Fin m → MvPolynomial (Fin (D + D)) K :=
  fun i => variableEquiv (liftVector b i)

def decodeUnknown (z : Fin (n + m * D) → MvPolynomial (Fin (D + D)) K) :
    (Fin n ⊕ (Fin m × Fin D)) → Poly K D :=
  fun i => variableEquiv.symm (z (unknownEquiv i))

def encodeUnknown (z : (Fin n ⊕ (Fin m × Fin D)) → Poly K D) :
    Fin (n + m * D) → MvPolynomial (Fin (D + D)) K :=
  fun i => variableEquiv (z (unknownEquiv.symm i))

@[simp] theorem decode_encode (z : (Fin n ⊕ (Fin m × Fin D)) → Poly K D) :
    decodeUnknown (encodeUnknown z) = z := by
  funext i
  simp [decodeUnknown, encodeUnknown]

@[simp] theorem encode_decode (z : Fin (n + m * D) → MvPolynomial (Fin (D + D)) K) :
    encodeUnknown (decodeUnknown z) = z := by
  funext i
  simp [decodeUnknown, encodeUnknown]

theorem indexed_mulVec (A : Matrix (Fin m) (Fin n) (Laurent K D))
    (z : Fin (n + m * D) → MvPolynomial (Fin (D + D)) K) (i : Fin m) :
    (indexedMatrix A *ᵥ z) i =
      variableEquiv ((expandedMatrix A *ᵥ decodeUnknown z) i) := by
  rw [indexedMatrix, Matrix.submatrix_mulVec_equiv]
  simp [Matrix.mulVec, dotProduct, decodeUnknown, Function.comp_def]

theorem indexed_solution_iff (A : Matrix (Fin m) (Fin n) (Laurent K D))
    (b : Fin m → Laurent K D)
    (z : Fin (n + m * D) → MvPolynomial (Fin (D + D)) K) :
    indexedMatrix A *ᵥ z = indexedRhs b ↔
      expandedMatrix A *ᵥ decodeUnknown z = liftVector b := by
  constructor
  · intro h
    funext i
    apply variableEquiv.injective
    exact (indexed_mulVec A z i).symm.trans (congrFun h i)
  · intro h
    funext i
    rw [indexed_mulVec, h]
    rfl

theorem indexed_solvable_iff (A : Matrix (Fin m) (Fin n) (Laurent K D))
    (b : Fin m → Laurent K D) :
    (∃ y, A *ᵥ y = b) ↔ ∃ z, indexedMatrix A *ᵥ z = indexedRhs b := by
  rw [polynomial_solution_iff]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨encodeUnknown z, (indexed_solution_iff A b _).mpr ?_⟩
    simpa using hz
  · rintro ⟨z, hz⟩
    exact ⟨decodeUnknown z, (indexed_solution_iff A b z).mp hz⟩

theorem indexedMatrix_degree (A : Matrix (Fin m) (Fin n) (Laurent K D))
    (h : ℕ) (hA : LaurentBoxes.MatrixSupported A h) :
    ∀ i j, (indexedMatrix A i j).totalDegree ≤ max (2 * D * h) 2 := by
  intro i j
  change (variableEquiv (expandedMatrix A i (unknownEquiv.symm j))).totalDegree ≤ _
  rw [variableEquiv_degree]
  exact expandedMatrix_degree A h hA i _

theorem indexedRhs_degree (b : Fin m → Laurent K D)
    (h : ℕ) (hb : ∀ i, LaurentBoxes.Supported (b i) h) :
    ∀ i, (indexedRhs b i).totalDegree ≤ max (2 * D * h) 2 := by
  intro i
  change (variableEquiv (liftVector b i)).totalDegree ≤ _
  rw [variableEquiv_degree]
  exact (liftVector_degree b h hb i).trans (le_max_left _ _)

end
end Decoupling.HighDim.LaurentPresentation
