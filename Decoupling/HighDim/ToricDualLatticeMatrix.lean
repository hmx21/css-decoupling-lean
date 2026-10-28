import Decoupling.HighDim.ToricDualLattice
import Decoupling.HighDim.ToricBoundaryCoordinates

/-! # The dual-cell identification as an actual invertible Laurent matrix -/

namespace Decoupling.HighDim.Toric

open Matrix Koszul

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [CommRing K] {D k l : ℕ}

def dualLatticeCoordinates (h : k + l = D) :
    CSS.Free K D (cellCount D k) ≃ₗ[Laurent K D] CSS.Free K D (cellCount D l) :=
  (cellCoordinates K D k).symm.trans
    ((Hodge.dualLattice K h).trans (dualCellCoordinates K l))

def dualLatticeMatrix (h : k + l = D) :
    Matrix (Fin (cellCount D l)) (Fin (cellCount D k)) (Laurent K D) :=
  LinearMap.toMatrix' (dualLatticeCoordinates K h).toLinearMap

@[simp] theorem dualLatticeMatrix_mulVec (h : k + l = D)
    (x : CSS.Free K D (cellCount D k)) :
    dualLatticeMatrix K h *ᵥ x = dualLatticeCoordinates K h x :=
  LinearMap.toMatrix'_mulVec _ _

theorem dualLatticeMatrix_boundary (h : k + 1 + l = D) :
    dualLatticeMatrix K (by omega : k + (l + 1) = D) * boundaryMatrix K D k =
      dagger (boundaryMatrix K D l) * dualLatticeMatrix K h := by
  apply Matrix.mulVec_injective
  funext x
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dualLatticeMatrix_mulVec,
    dualLatticeMatrix_mulVec, boundaryMatrix_apply]
  simp only [dualLatticeCoordinates, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  rw [← dualCellCoordinates_precomp_bar]
  have he := congrArg (fun L => L ((cellCoordinates K D (k + 1)).symm x))
    (Hodge.dualLattice_boundary K h)
  exact congrArg (dualCellCoordinates K (l + 1)) he

theorem dualCellCoordinates_apply (k : ℕ)
    (f : Module.Dual (Laurent K D) (Term (Laurent K D) D k))
    (i : Fin (cellCount D k)) :
    dualCellCoordinates K k f i = f (Finsupp.single ((Fintype.equivFin (Cell D k)).symm i) 1) := by
  simp [dualCellCoordinates, piDualCoordinates, Module.Basis.constr_symm_apply,
    Pi.basisFun_apply, cellCoordinates_symm_single]

def complementaryIndex (h : k + l = D) : Fin (cellCount D k) ≃ Fin (cellCount D l) :=
  (Fintype.equivFin (Cell D k)).symm.trans
    ((Hodge.complementEquiv h).trans (Fintype.equivFin (Cell D l)))

def dualCellUnit (I : Cell D k) : (Laurent K D)ˣ :=
  Hodge.orientationUnit (Laurent K D) I * Hodge.cellUnit (Laurent K D) (Hodge.directionUnit K) I

theorem dualLatticeMatrix_entry (h : k + l = D)
    (i : Fin (cellCount D l)) (j : Fin (cellCount D k)) :
    dualLatticeMatrix K h i j = if complementaryIndex h j = i then
      (dualCellUnit K ((Fintype.equivFin (Cell D k)).symm j) : Laurent K D) else 0 := by
  have hm := congrFun (dualLatticeMatrix_mulVec K h (Pi.single j 1)) i
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at hm
  rw [hm]
  simp only [dualLatticeCoordinates, LinearEquiv.trans_apply, cellCoordinates_symm_single,
    dualCellCoordinates_apply, Hodge.dualLattice, Hodge.laurentGauge]
  rw [Hodge.gauge_single]
  have hs (I : Cell D k) : Finsupp.single I (Hodge.cellUnit (Laurent K D) (Hodge.directionUnit K) I : Laurent K D) =
      (Hodge.cellUnit (Laurent K D) (Hodge.directionUnit K) I : Laurent K D) • Finsupp.single I 1 := by simp
  simp only [mul_one]
  rw [hs, map_smul, LinearMap.smul_apply, smul_eq_mul, Hodge.duality_single_single]
  have hi : complementaryIndex h j = i ↔
      Hodge.complement h ((Fintype.equivFin (Cell D k)).symm j) =
        (Fintype.equivFin (Cell D l)).symm i := by
    change (Fintype.equivFin (Cell D l))
      (Hodge.complement h ((Fintype.equivFin (Cell D k)).symm j)) = i ↔ _
    exact (Equiv.eq_symm_apply _).symm
  by_cases hji : complementaryIndex h j = i
  · simp [hji, hi.mp hji, dualCellUnit, Hodge.orientationUnit, mul_comm]
  · simp [hji, mt hi.mpr hji]

end
end Decoupling.HighDim.Toric
