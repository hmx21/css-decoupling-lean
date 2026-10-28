import Decoupling.HighDim.AlgorithmTwoFiniteComplexPlacement
import Decoupling.HighDim.AlgorithmTwoFiniteComplexContraction

/-!
# Pure degree-fiber slices of actual finite-complex differential arrays

A slice has the original source and target term ranks. In particular,
zero rows from other grades are not retained as spurious homology.
-/
namespace Decoupling.HighDim.AlgorithmTwoFiniteComplex
open CategoryTheory Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D h length : ℕ}

def sliceBlock {rank : Fin length → ℕ}
    (A : LaurentArithmetic.DenseMatrix K D (∑ i, rank i) (∑ i, rank i) h)
    (row col : Fin length) : LaurentArithmetic.DenseMatrix K D (rank row) (rank col) h :=
  Vector.ofFn fun a => Vector.ofFn fun b =>
    A[finSigmaFinEquiv ⟨row,a⟩][finSigmaFinEquiv ⟨col,b⟩]

theorem sliceBlock_denote {rank : Fin length → ℕ}
    (A : LaurentArithmetic.DenseMatrix K D (∑ i, rank i) (∑ i, rank i) h)
    (row col : Fin length) :
    LaurentArithmetic.matrixDenote (sliceBlock A row col) =
      (LaurentArithmetic.matrixDenote A).submatrix (fun a => finSigmaFinEquiv ⟨row,a⟩)
        (fun b => finSigmaFinEquiv ⟨col,b⟩) := by
  funext a b
  simp only [LaurentArithmetic.matrixDenote, sliceBlock, Fin.getElem_fin, Vector.getElem_ofFn,
    Fin.eta, Matrix.submatrix_apply]

noncomputable section
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}

theorem bounded_embed_single (c : StableFree.Coordinates C) (lo : ℤ) (length : ℕ)
    (outside : ∀ j, j < lo ∨ lo+length ≤ j → c.rank j = 0)
    (i : Fin length) (a : Fin (c.rank (lo+i))) :
    (Coordinates.ofBounded c lo length outside).embed (lo+i)
      ((c.equiv (lo+i)).symm (Pi.single a 1)) = Pi.single (finSigmaFinEquiv ⟨i,a⟩) 1 := by
  funext v
  obtain ⟨⟨j,b⟩,rfl⟩ := (finSigmaFinEquiv (n := fun i : Fin length => c.rank (lo+i))).surjective v
  rw [bounded_embed_at]
  by_cases hj : j=i
  · subst j
    simp [Pi.single_apply]
  · have hd : lo+(j:ℤ) ≠ lo+i := by intro hh; apply hj; apply Fin.ext; omega
    rw [dite_eq_right hd]
    have hv : (finSigmaFinEquiv (n := fun s : Fin length => c.rank (lo+s))) ⟨i,a⟩ ≠
        finSigmaFinEquiv ⟨j,b⟩ := by
      intro hv
      exact hj (congrArg Sigma.fst (finSigmaFinEquiv.injective hv)).symm
    simp only [Pi.single_apply, ite_eq_right (Ne.symm hv)]

theorem sliceBlock_entry (c : StableFree.Coordinates C) (lo : ℤ) (length : ℕ)
    (outside : ∀ j, j < lo ∨ lo+length ≤ j → c.rank j = 0)
    (A : LaurentArithmetic.DenseMatrix K D (totalRank c.rank lo length) (totalRank c.rank lo length) h)
    (hA : (Coordinates.ofBounded c lo length outside).RepresentsDifferential (LaurentArithmetic.matrixDenote A))
    (row col : Fin length) (hrow : lo+(row:ℤ) = lo+col+1)
    (a : Fin (c.rank (lo+row))) (b : Fin (c.rank (lo+col))) :
    LaurentArithmetic.matrixDenote (sliceBlock A row col) a b =
      c.equiv (lo+row) ((C.d (lo+col) (lo+row)).hom
        ((c.equiv (lo+col)).symm (Pi.single b 1))) a := by
  have he := congrFun (represents_at (Coordinates.ofBounded c lo length outside) _ hA
    (lo+col) (lo+row) hrow ((c.equiv (lo+col)).symm (Pi.single b 1))) (finSigmaFinEquiv ⟨row,a⟩)
  rw [bounded_embed_single, bounded_embed_at] at he
  rw [sliceBlock_denote]
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using he

theorem sliceBlock_linearMap (c : StableFree.Coordinates C) (lo : ℤ) (length : ℕ)
    (outside : ∀ j, j < lo ∨ lo+length ≤ j → c.rank j = 0)
    (A : LaurentArithmetic.DenseMatrix K D (totalRank c.rank lo length) (totalRank c.rank lo length) h)
    (hA : (Coordinates.ofBounded c lo length outside).RepresentsDifferential (LaurentArithmetic.matrixDenote A))
    (row col : Fin length) (hrow : lo+(row:ℤ) = lo+col+1) :
    (LaurentArithmetic.matrixDenote (sliceBlock A row col)).mulVecLin =
      (c.equiv (lo+row)).toLinearMap.comp
        ((C.d (lo+col) (lo+row)).hom.comp (c.equiv (lo+col)).symm.toLinearMap) := by
  apply (Pi.basisFun (Laurent K D) (Fin (c.rank (lo+col)))).ext
  intro b
  funext a
  simpa [Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
    Pi.single_apply, mul_ite] using sliceBlock_entry c lo length outside A hA row col hrow a b

/-- Native original-coordinate contract consumed by the actual cohomology
window, with no full-total-rank padding in the window modules. -/
theorem sliceBlock_differential (c : StableFree.Coordinates C) (lo : ℤ) (length : ℕ)
    (outside : ∀ j, j < lo ∨ lo+length ≤ j → c.rank j = 0)
    (A : LaurentArithmetic.DenseMatrix K D (totalRank c.rank lo length) (totalRank c.rank lo length) h)
    (hA : (Coordinates.ofBounded c lo length outside).RepresentsDifferential (LaurentArithmetic.matrixDenote A))
    (row col : Fin length) (hrow : lo+(row:ℤ) = lo+col+1) (x : C.X (lo+col)) :
    LaurentArithmetic.matrixDenote (sliceBlock A row col) *ᵥ c.equiv (lo+col) x =
      c.equiv (lo+row) ((C.d (lo+col) (lo+row)).hom x) := by
  change (LaurentArithmetic.matrixDenote (sliceBlock A row col)).mulVecLin (c.equiv (lo+col) x) = _
  rw [sliceBlock_linearMap c lo length outside A hA row col hrow]
  simp

end
end Decoupling.HighDim.AlgorithmTwoFiniteComplex
