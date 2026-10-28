import Decoupling.HighDim.ToricHodgeExact

/-!
# Actual matrix coordinates of the dual toric differential

The transpose is obtained from the genuine module dual. The Laurent
antipode then converts this into the dagger used by CSS checks.
-/

namespace Decoupling.HighDim.Toric

open Matrix Koszul

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [CommRing K] {D : ℕ}

def piDualCoordinates (n : ℕ) :
    Module.Dual (Laurent K D) (CSS.Free K D n) ≃ₗ[Laurent K D] CSS.Free K D n :=
  ((Pi.basisFun (Laurent K D) (Fin n)).constr (Laurent K D)).symm

theorem piDualCoordinates_evaluate (n : ℕ)
    (f : Module.Dual (Laurent K D) (CSS.Free K D n)) (v : CSS.Free K D n) :
    f v = ∑ i, v i * piDualCoordinates K n f i := by
  have h := congrArg (fun z => f z) ((Pi.basisFun (Laurent K D) (Fin n)).sum_repr v)
  simpa only [map_sum, map_smul, smul_eq_mul, Pi.basisFun_repr, piDualCoordinates, Module.Basis.constr_symm_apply] using h.symm

def dualCellCoordinates (k : ℕ) :
    Module.Dual (Laurent K D) (Term (Laurent K D) D k) ≃ₗ[Laurent K D]
      CSS.Free K D (cellCount D k) :=
  (cellCoordinates K D k).symm.dualMap.trans (piDualCoordinates K (cellCount D k))

theorem dualCellCoordinates_evaluate (k : ℕ)
    (f : Module.Dual (Laurent K D) (Term (Laurent K D) D k)) (v : Term (Laurent K D) D k) :
    f v = ∑ i, cellCoordinates K D k v i * dualCellCoordinates K k f i := by
  simpa only [LinearEquiv.dualMap_apply, LinearEquiv.symm_apply_apply, dualCellCoordinates,
    LinearEquiv.trans_apply] using
    piDualCoordinates_evaluate K (cellCount D k) ((cellCoordinates K D k).symm.dualMap f)
      (cellCoordinates K D k v)

theorem dualCellCoordinates_precomp (k : ℕ)
    (f : Module.Dual (Laurent K D) (Term (Laurent K D) D k)) :
    dualCellCoordinates K (k + 1) ((boundary (Laurent K D) (difference K) k).hom.dualMap f) =
      (boundaryMatrix K D k).transpose *ᵥ dualCellCoordinates K k f := by
  funext i
  simp only [dualCellCoordinates, LinearEquiv.trans_apply, piDualCoordinates,
    Module.Basis.constr_symm_apply, Pi.basisFun_apply, LinearEquiv.dualMap_apply,
    LinearMap.dualMap_apply]
  change f (boundary (Laurent K D) (difference K) k
      ((cellCoordinates K D (k + 1)).symm (Pi.single i 1))) = _
  rw [dualCellCoordinates_evaluate]
  have h := boundaryMatrix_apply K D k (Pi.single i 1)
  rw [← h]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, dualCellCoordinates,
    piDualCoordinates, Module.Basis.constr_symm_apply, Pi.basisFun_apply]

def barVector {n : ℕ} (v : CSS.Free K D n) : CSS.Free K D n := fun i => bar (v i)

@[simp] theorem barVector_involutive {n : ℕ} (v : CSS.Free K D n) :
    barVector K (barVector K v) = v := by ext i; simp [barVector]

theorem barVector_injective {n : ℕ} : Function.Injective (barVector K (D := D) (n := n)) :=
  Function.LeftInverse.injective (barVector_involutive K)

theorem barVector_dagger_mulVec {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (Laurent K D)) (v : CSS.Free K D m) :
    barVector K (dagger A *ᵥ v) = A.transpose *ᵥ barVector K v := by
  ext i
  simp [barVector, dagger, Matrix.mulVec, dotProduct]

end
end Decoupling.HighDim.Toric
