import Decoupling.HighDim.ToricStackChecks
import Mathlib.Data.Matrix.Block

/-! # Actual block matrices in the fixed toric-stack coordinates -/

namespace Decoupling.HighDim.Toric

open CategoryTheory Matrix

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [Field K] (D : ℕ) {ι : Type} [Fintype ι]

@[simp] theorem flattenCoordinates_symm_apply (counts : ι → ℕ)
    (v : Fin (Fintype.card (Σ i, Fin (counts i))) → Laurent K D) (i : ι) (j : Fin (counts i)) :
    (flattenCoordinates K D counts).symm v i j = v ((Fintype.equivFin _) ⟨i, j⟩) := by
  simp [flattenCoordinates, LinearEquiv.piCongrLeft', Sigma.curry]

@[simp] theorem flattenCoordinates_apply (counts : ι → ℕ)
    (v : ∀ i, Fin (counts i) → Laurent K D) (i : ι) (j : Fin (counts i)) :
    flattenCoordinates K D counts v ((Fintype.equivFin _) ⟨i, j⟩) = v i j := by
  simp [flattenCoordinates]
  rfl

def stackMatrix {rows cols : ι → ℕ}
    (B : ∀ i, Matrix (Fin (rows i)) (Fin (cols i)) (Laurent K D)) :
    Matrix (Fin (Fintype.card (Σ i, Fin (rows i))))
      (Fin (Fintype.card (Σ i, Fin (cols i)))) (Laurent K D) :=
  (Matrix.blockDiagonal' B).submatrix (Fintype.equivFin _).symm (Fintype.equivFin _).symm

theorem stackMatrix_apply {rows cols : ι → ℕ}
    (B : ∀ i, Matrix (Fin (rows i)) (Fin (cols i)) (Laurent K D))
    (v : CSS.Free K D (Fintype.card (Σ i, Fin (cols i)))) (i : ι) :
    (flattenCoordinates K D rows).symm (stackMatrix K D B *ᵥ v) i =
      B i *ᵥ (flattenCoordinates K D cols).symm v i := by
  classical
  funext j
  simp only [flattenCoordinates_symm_apply, stackMatrix, Matrix.mulVec, dotProduct,
    Matrix.submatrix_apply, Equiv.symm_apply_apply]
  rw [← (Fintype.equivFin (Σ i, Fin (cols i))).sum_comp]
  rw [Fintype.sum_sigma]
  simp [Matrix.blockDiagonal'_apply']

theorem stackMatrix_mul {rows middle cols : ι → ℕ}
    (A : ∀ i, Matrix (Fin (rows i)) (Fin (middle i)) (Laurent K D))
    (B : ∀ i, Matrix (Fin (middle i)) (Fin (cols i)) (Laurent K D)) :
    stackMatrix K D A * stackMatrix K D B = stackMatrix K D (fun i => A i * B i) := by
  classical
  simp only [stackMatrix, Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]

theorem stackMatrix_one (rows : ι → ℕ) :
    stackMatrix K D (fun i => (1 : Matrix (Fin (rows i)) (Fin (rows i)) (Laurent K D))) = 1 := by
  apply Matrix.mulVec_injective
  funext v
  apply (flattenCoordinates K D rows).symm.injective
  funext i
  rw [stackMatrix_apply, Matrix.one_mulVec, Matrix.one_mulVec]

theorem stackMatrix_dagger {rows cols : ι → ℕ}
    (B : ∀ i, Matrix (Fin (rows i)) (Fin (cols i)) (Laurent K D)) :
    dagger (stackMatrix K D B) = stackMatrix K D (fun i => dagger (B i)) := by
  classical
  have hb : dagger (Matrix.blockDiagonal' B) = Matrix.blockDiagonal' (fun i => dagger (B i)) := by
    change (Matrix.blockDiagonal' B).transpose.map bar = _
    rw [Matrix.blockDiagonal'_transpose, Matrix.blockDiagonal'_map _ _ bar_zero]
    rfl
  change (dagger (Matrix.blockDiagonal' B)).submatrix _ _ = _
  rw [hb]
  rfl

variable (forms : ι → ℕ)

theorem stackCoordinates_unflatten (offset : ℕ)
    (x : (stackModel K D forms).X (1 - offset)) (i : ι) :
    (flattenCoordinates K D (fun i => cellCount D (forms i + offset))).symm
      (stackCoordinates K D forms offset x) i =
    cellCoordinates K D (forms i + offset)
      (((Koszul.laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE (forms i + 1))
        (i := forms i + offset) (i' := 1 - offset) (by simp)).hom
        ((stackTermIso K D forms (1 - offset)).hom x i)) := by
  simp [stackCoordinates]
  rfl

theorem stackCoordinates_d_unflatten (offset : ℕ)
    (x : (stackModel K D forms).X (1 - (offset + 1 : ℕ))) (i : ι) :
    (flattenCoordinates K D (fun i => cellCount D (forms i + offset))).symm
      (stackCoordinates K D forms offset
        ((stackModel K D forms).d (1 - (offset + 1 : ℕ)) (1 - offset) x)) i =
      boundaryMatrix K D (forms i + offset) *ᵥ
        (flattenCoordinates K D (fun i => cellCount D (forms i + (offset + 1)))).symm
          (stackCoordinates K D forms (offset + 1) x) i := by
  rw [stackCoordinates_unflatten, stackCoordinates_unflatten, boundaryMatrix_apply]
  erw [LinearEquiv.symm_apply_apply]
  rw [stackTermIso_d]
  dsimp only [model]
  rw [(Koszul.laurentComplex K D).extend_d_eq (ComplexShape.embeddingUpIntLE (forms i + 1))
    (i := forms i + offset + 1) (j := forms i + offset)
    (i' := 1 - (offset + 1 : ℕ)) (j' := 1 - offset) (by simp) (by simp)]
  simp [Koszul.laurentComplex]
  rfl

theorem stackBoundaryMatrix_eq_stackMatrix (offset : ℕ) :
    stackBoundaryMatrix K D forms offset =
      stackMatrix K D (fun i => boundaryMatrix K D (forms i + offset)) := by
  apply Matrix.mulVec_injective
  funext v
  apply (flattenCoordinates K D (fun i => cellCount D (forms i + offset))).symm.injective
  funext i
  rw [stackMatrix_apply, stackBoundaryMatrix_apply, stackCoordinates_d_unflatten,
    LinearEquiv.apply_symm_apply]
  rfl

end
end Decoupling.HighDim.Toric
