import Decoupling.HighDim.ToricHodgeCoordinates

/-! # Matrix coordinates of arbitrary directional Koszul weights -/

namespace Decoupling.HighDim.Toric

open Matrix Koszul

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [CommRing K] {D : ℕ}

@[simp] theorem cellCoordinates_apply (k : ℕ) (v : Term (Laurent K D) D k)
    (i : Fin (cellCount D k)) :
    cellCoordinates K D k v i = v ((Fintype.equivFin (Cell D k)).symm i) := by
  simp [cellCoordinates]

@[simp] theorem cellCoordinates_symm_single (k : ℕ) (i : Fin (cellCount D k)) :
    (cellCoordinates K D k).symm (Pi.single i 1) =
      Finsupp.single ((Fintype.equivFin (Cell D k)).symm i) 1 := by
  apply (cellCoordinates K D k).injective
  rw [LinearEquiv.apply_symm_apply]
  funext j
  simp [Finsupp.single_apply, Pi.single_apply, eq_comm]

def weightedBoundaryMatrix (w : Fin D → Laurent K D) (k : ℕ) :
    Matrix (Fin (cellCount D k)) (Fin (cellCount D (k + 1))) (Laurent K D) :=
  LinearMap.toMatrix' ((cellCoordinates K D k).toLinearMap.comp
    ((boundary (Laurent K D) w k).hom.comp
      (cellCoordinates K D (k + 1)).symm.toLinearMap))

theorem weightedBoundaryMatrix_apply (w : Fin D → Laurent K D) (k : ℕ)
    (v : CSS.Free K D (cellCount D (k + 1))) :
    weightedBoundaryMatrix K w k *ᵥ v = cellCoordinates K D k
      (boundary (Laurent K D) w k ((cellCoordinates K D (k + 1)).symm v)) :=
  LinearMap.toMatrix'_mulVec _ _

theorem weightedBoundaryMatrix_entry (w : Fin D → Laurent K D) (k : ℕ)
    (i : Fin (cellCount D k)) (j : Fin (cellCount D (k + 1))) :
    weightedBoundaryMatrix K w k i j =
      ∑ a : Fin (k + 1), if face ((Fintype.equivFin (Cell D (k + 1))).symm j) a =
          (Fintype.equivFin (Cell D k)).symm i
        then (-1 : Laurent K D) ^ a.val * w ((Fintype.equivFin (Cell D (k + 1))).symm j a)
        else 0 := by
  classical
  have h := congrFun (weightedBoundaryMatrix_apply K w k (Pi.single j 1)) i
  rw [cellCoordinates_symm_single, boundary_basis, cellCoordinates_apply] at h
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply,
    Finsupp.sum_apply, Finsupp.single_apply] using h

theorem weightedBoundaryMatrix_bar (w : Fin D → Laurent K D) (k : ℕ) :
    weightedBoundaryMatrix K (fun i => bar (w i)) k =
      fun i j => bar (weightedBoundaryMatrix K w k i j) := by
  classical
  funext i j
  simp [weightedBoundaryMatrix_entry, map_sum, apply_ite bar]

theorem dualCellCoordinates_precomp_weighted (w : Fin D → Laurent K D) (k : ℕ)
    (f : Module.Dual (Laurent K D) (Term (Laurent K D) D k)) :
    dualCellCoordinates K (k + 1) ((boundary (Laurent K D) w k).hom.dualMap f) =
      (weightedBoundaryMatrix K w k).transpose *ᵥ dualCellCoordinates K k f := by
  funext i
  simp only [dualCellCoordinates, LinearEquiv.trans_apply, piDualCoordinates,
    Module.Basis.constr_symm_apply, Pi.basisFun_apply, LinearEquiv.dualMap_apply,
    LinearMap.dualMap_apply]
  change f (boundary (Laurent K D) w k
      ((cellCoordinates K D (k + 1)).symm (Pi.single i 1))) = _
  rw [dualCellCoordinates_evaluate]
  have h := weightedBoundaryMatrix_apply K w k (Pi.single i 1)
  rw [← h]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, dualCellCoordinates,
    piDualCoordinates, Module.Basis.constr_symm_apply, Pi.basisFun_apply]

theorem dualCellCoordinates_precomp_bar (k : ℕ)
    (f : Module.Dual (Laurent K D) (Term (Laurent K D) D k)) :
    dualCellCoordinates K (k + 1)
        ((boundary (Laurent K D) (fun i => bar (difference K i)) k).hom.dualMap f) =
      dagger (boundaryMatrix K D k) *ᵥ dualCellCoordinates K k f := by
  rw [dualCellCoordinates_precomp_weighted, weightedBoundaryMatrix_bar]
  rfl

end
end Decoupling.HighDim.Toric
