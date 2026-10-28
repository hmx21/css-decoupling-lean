import Decoupling.HighDim.ToricStackMatrices
import Decoupling.HighDim.ToricDualLatticeSites

/-!
# Actual complementary dual-lattice identification for finite toric stacks

The block diagonal is expressed in the same fixed finite enumeration as
`stackChecks`. Both dagger inverse identities and both stabilizer images
follow from the single-copy theorems through proved matrix equalities.
The index type may be empty.
-/

namespace Decoupling.HighDim.Toric

open Matrix Koszul

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [Field K] (D : ℕ) {ι : Type} [Fintype ι]
  (forms complements : ι → ℕ)

def stackDualCellMatrix (r s : ℕ) (h : ∀ i, (forms i + r) + (complements i + s) = D) :
    Matrix (Fin (stackCount D complements s)) (Fin (stackCount D forms r)) (Laurent K D) :=
  stackMatrix K D (fun i => dualLatticeMatrix K (h i))

theorem stackDualCellMatrix_dagger_mul (r s : ℕ)
    (h : ∀ i, (forms i + r) + (complements i + s) = D) :
    dagger (stackDualCellMatrix K D forms complements r s h) *
      stackDualCellMatrix K D forms complements r s h = 1 := by
  rw [stackDualCellMatrix, stackMatrix_dagger, stackMatrix_mul]
  simp only [dualLatticeMatrix_dagger_mul]
  exact stackMatrix_one K D _

theorem stackDualCellMatrix_mul_dagger (r s : ℕ)
    (h : ∀ i, (forms i + r) + (complements i + s) = D) :
    stackDualCellMatrix K D forms complements r s h *
      dagger (stackDualCellMatrix K D forms complements r s h) = 1 := by
  rw [stackDualCellMatrix, stackMatrix_dagger, stackMatrix_mul]
  simp only [dualLatticeMatrix_mul_dagger]
  exact stackMatrix_one K D _

variable (h : ∀ i, forms i + complements i + 2 = D)

def stackDualMatrix : Matrix (Fin (stackCount D complements 1))
    (Fin (stackCount D forms 1)) (Laurent K D) :=
  stackDualCellMatrix K D forms complements 1 1 (fun i => by have := h i; omega)

theorem stackDualMatrix_dagger_mul :
    dagger (stackDualMatrix K D forms complements h) *
      stackDualMatrix K D forms complements h = 1 :=
  stackDualCellMatrix_dagger_mul K D forms complements 1 1 _

theorem stackDualMatrix_mul_dagger :
    stackDualMatrix K D forms complements h *
      dagger (stackDualMatrix K D forms complements h) = 1 :=
  stackDualCellMatrix_mul_dagger K D forms complements 1 1 _

theorem stackDualMatrix_x_square :
    stackDualMatrix K D forms complements h * stackBoundaryMatrix K D forms 1 =
      dagger (stackBoundaryMatrix K D complements 0) *
        stackDualCellMatrix K D forms complements 2 0 (fun i => by have := h i; omega) := by
  rw [stackBoundaryMatrix_eq_stackMatrix, stackBoundaryMatrix_eq_stackMatrix,
    stackMatrix_dagger]
  simp only [stackDualMatrix, stackDualCellMatrix, stackMatrix_mul]
  congr 1
  funext i
  exact dualLatticeMatrix_boundary K (by have := h i; omega)

theorem stackDualMatrix_z_square :
    stackDualMatrix K D forms complements h * dagger (stackBoundaryMatrix K D forms 0) =
      stackBoundaryMatrix K D complements 1 *
        stackDualCellMatrix K D forms complements 0 2 (fun i => by have := h i; omega) := by
  rw [stackBoundaryMatrix_eq_stackMatrix, stackBoundaryMatrix_eq_stackMatrix,
    stackMatrix_dagger]
  simp only [stackDualMatrix, stackDualCellMatrix, stackMatrix_mul]
  congr 1
  funext i
  exact dualLatticeMatrix_coboundary K (h i)

private theorem image_of_invertible_square {a b c d : ℕ}
    (U : Matrix (Fin b) (Fin a) (Laurent K D))
    (B : Matrix (Fin a) (Fin c) (Laurent K D))
    (B' : Matrix (Fin b) (Fin d) (Laurent K D))
    (P : Matrix (Fin d) (Fin c) (Laurent K D))
    (hP : P * dagger P = 1) (hs : U * B = B' * P) (v : CSS.Free K D b) :
    (∃ z, U *ᵥ (B *ᵥ z) = v) ↔ ∃ z, B' *ᵥ z = v := by
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨P *ᵥ z, ?_⟩
    simpa only [Matrix.mulVec_mulVec, ← hs] using hz
  · rintro ⟨z, hz⟩
    refine ⟨dagger P *ᵥ z, ?_⟩
    simp only [Matrix.mulVec_mulVec]
    rw [← Matrix.mul_assoc, hs, Matrix.mul_assoc, hP, Matrix.mul_one, hz]

theorem stackDual_z_stabilizers (v : CSS.Free K D (stackCount D complements 1)) :
    (∃ z, stackDualMatrix K D forms complements h *ᵥ
      (dagger (stackChecks K D forms).swap.H_Z *ᵥ z) = v) ↔
        ∃ z, dagger (stackChecks K D complements).H_Z *ᵥ z = v := by
  change (∃ z, stackDualMatrix K D forms complements h *ᵥ
    (dagger (stackBoundaryMatrix K D forms 0) *ᵥ z) = v) ↔ _
  rw [stackChecks_dagger_H_Z]
  exact image_of_invertible_square K D _ _ _ _
    (stackDualCellMatrix_mul_dagger K D forms complements 0 2 _)
    (stackDualMatrix_z_square K D forms complements h) v

theorem stackDual_x_stabilizers (v : CSS.Free K D (stackCount D complements 1)) :
    (∃ z, stackDualMatrix K D forms complements h *ᵥ
      (dagger (stackChecks K D forms).swap.H_X *ᵥ z) = v) ↔
        ∃ z, dagger (stackChecks K D complements).H_X *ᵥ z = v := by
  change (∃ z, stackDualMatrix K D forms complements h *ᵥ
    (dagger (stackChecks K D forms).H_Z *ᵥ z) = v) ↔ _
  rw [stackChecks_dagger_H_Z, stackChecks_H_X]
  exact image_of_invertible_square K D _ _ _ _
    (stackDualCellMatrix_mul_dagger K D forms complements 2 0 _)
    (stackDualMatrix_x_square K D forms complements h) v

end
end Decoupling.HighDim.Toric
