import Decoupling.HighDim.AlgorithmTwoFiniteComplexSlice

/-! # Pure original-coordinate slices of arbitrary maps and homotopies -/
namespace Decoupling.HighDim.AlgorithmTwoFiniteComplex
open CategoryTheory Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D h N M q r : ℕ}

def sliceMap (A : LaurentArithmetic.DenseMatrix K D N M h)
    (rows : Vector (Fin N) q) (cols : Vector (Fin M) r) : LaurentArithmetic.DenseMatrix K D q r h :=
  Vector.ofFn fun i => Vector.ofFn fun j => A[rows.get i][cols.get j]

theorem sliceMap_denote (A : LaurentArithmetic.DenseMatrix K D N M h)
    (rows : Vector (Fin N) q) (cols : Vector (Fin M) r) :
    LaurentArithmetic.matrixDenote (sliceMap A rows cols) =
      (LaurentArithmetic.matrixDenote A).submatrix rows.get cols.get := by
  funext i j
  simp only [sliceMap, LaurentArithmetic.matrixDenote, Fin.getElem_fin, Vector.getElem_ofFn,
    Fin.eta, Matrix.submatrix_apply]

def slotSelector {length : ℕ} (rank : Fin length → ℕ) (i : Fin length) :
    Vector (Fin (∑ i, rank i)) (rank i) := Vector.ofFn fun a => finSigmaFinEquiv ⟨i,a⟩

@[simp] theorem slotSelector_get {length : ℕ} (rank : Fin length → ℕ) (i : Fin length) (a : Fin (rank i)) :
    (slotSelector rank i).get a = finSigmaFinEquiv ⟨i,a⟩ := by
  change (Vector.ofFn _)[a.val] = _
  rw [Vector.getElem_ofFn]

noncomputable section
variable {T C : CochainComplex (ModuleCat (Laurent K D)) ℤ}

/-- Generic selector contract: rows read original target coordinates and
columns are the actual embedded original source unit vectors. -/
theorem sliceMap_native (cT : Coordinates T M) (cC : Coordinates C N) (a b : ℤ)
    (eT : T.X a ≃ₗ[Laurent K D] (Fin r → Laurent K D))
    (eC : C.X b ≃ₗ[Laurent K D] (Fin q → Laurent K D))
    (rows : Vector (Fin N) q) (cols : Vector (Fin M) r)
    (hrows : ∀ x i, cC.embed b x (rows.get i) = eC x i)
    (hcols : ∀ j, cT.embed a (eT.symm (Pi.single j 1)) = Pi.single (cols.get j) 1)
    (A : LaurentArithmetic.DenseMatrix K D N M h) (f : T.X a →ₗ[Laurent K D] C.X b)
    (hA : ∀ x, LaurentArithmetic.matrixDenote A *ᵥ cT.embed a x = cC.embed b (f x))
    (x : T.X a) :
    LaurentArithmetic.matrixDenote (sliceMap A rows cols) *ᵥ eT x = eC (f x) := by
  have hm : (LaurentArithmetic.matrixDenote (sliceMap A rows cols)).mulVecLin =
      eC.toLinearMap.comp (f.comp eT.symm.toLinearMap) := by
    apply (Pi.basisFun (Laurent K D) (Fin r)).ext
    intro j
    funext i
    have he := congrFun (hA (eT.symm (Pi.single j 1))) (rows.get i)
    rw [hcols, hrows] at he
    rw [sliceMap_denote]
    simpa [Pi.basisFun_apply, Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct,
      Pi.single_apply, mul_ite] using he
  change (LaurentArithmetic.matrixDenote (sliceMap A rows cols)).mulVecLin (eT x) = _
  rw [hm]
  simp

/-- Original bounded degree-slot selectors discharge the generic contracts. -/
theorem sliceMap_between (cT : StableFree.Coordinates T) (cC : StableFree.Coordinates C)
    (loT loC : ℤ) (lengthT lengthC : ℕ)
    (outT : ∀ j, j < loT ∨ loT+lengthT ≤ j → cT.rank j = 0)
    (outC : ∀ j, j < loC ∨ loC+lengthC ≤ j → cC.rank j = 0)
    (row : Fin lengthC) (col : Fin lengthT)
    (A : LaurentArithmetic.DenseMatrix K D (totalRank cC.rank loC lengthC) (totalRank cT.rank loT lengthT) h)
    (f : T.X (loT+col) →ₗ[Laurent K D] C.X (loC+row))
    (hA : ∀ x, LaurentArithmetic.matrixDenote A *ᵥ
      (Coordinates.ofBounded cT loT lengthT outT).embed (loT+col) x =
      (Coordinates.ofBounded cC loC lengthC outC).embed (loC+row) (f x))
    (x : T.X (loT+col)) :
    LaurentArithmetic.matrixDenote (sliceMap A
      (slotSelector (fun i : Fin lengthC => cC.rank (loC+i)) row)
      (slotSelector (fun i : Fin lengthT => cT.rank (loT+i)) col)) *ᵥ cT.equiv (loT+col) x =
      cC.equiv (loC+row) (f x) := by
  apply sliceMap_native (Coordinates.ofBounded cT loT lengthT outT)
    (Coordinates.ofBounded cC loC lengthC outC) _ _ (cT.equiv _) (cC.equiv _)
    _ _ ?_ ?_ A f hA x
  · intro y i
    rw [slotSelector_get, bounded_embed_at]
    simp
  · intro j
    rw [slotSelector_get]
    exact bounded_embed_single cT loT lengthT outT col j

end
end Decoupling.HighDim.AlgorithmTwoFiniteComplex
