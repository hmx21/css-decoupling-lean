import Decoupling.HighDim.ToricConjugateTail
import Decoupling.HighDim.ToricBoundaryCoordinates

/-!
# The actual conjugate-dual tail differential in Hodge coordinates

Source: `drafts/main.tex`, the toric-profile calculation following the
finite free model of `𝒮_X`. These identities concern actual conjugated
modules and their linear Hom spaces over an arbitrary commutative ring.
-/

namespace Decoupling.HighDim.Toric

open CategoryTheory Matrix Koszul

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [CommRing K] {D : ℕ}

theorem conjugateCellEquiv_coordinates (n : ℕ)
    (v : Layers.conjugate (ModuleCat.of (Laurent K D) (Term (Laurent K D) D n))) :
    cellCoordinates K D n (conjugateCellEquiv K n v) =
      barVector K (cellCoordinates K D n (show Term (Laurent K D) D n from v)) := by
  funext i
  simp [cellCoordinates_apply, barVector]

theorem conjugateCellEquiv_boundary (n : ℕ) (w : Fin D → Laurent K D)
    (v : Layers.conjugate (ModuleCat.of (Laurent K D) (Term (Laurent K D) D (n + 1)))) :
    conjugateCellEquiv K n
      (show Layers.conjugate (ModuleCat.of (Laurent K D) (Term (Laurent K D) D n)) from
        boundary (Laurent K D) w n (show Term (Laurent K D) D (n + 1) from v)) =
      boundary (Laurent K D) (fun i => bar (w i)) n (conjugateCellEquiv K (n + 1) v) := by
  apply (cellCoordinates K D n).injective
  rw [conjugateCellEquiv_coordinates]
  change barVector K (cellCoordinates K D n
    (boundary (Laurent K D) w n (show Term (Laurent K D) D (n + 1) from v))) = _
  have h1 := weightedBoundaryMatrix_apply K w n
    (cellCoordinates K D (n + 1) (show Term (Laurent K D) D (n + 1) from v))
  have h2 := weightedBoundaryMatrix_apply K (fun i => bar (w i)) n
    (cellCoordinates K D (n + 1) (conjugateCellEquiv K (n + 1) v))
  simp only [LinearEquiv.symm_apply_apply] at h1 h2
  rw [← h1, ← h2, conjugateCellEquiv_coordinates, weightedBoundaryMatrix_bar]
  funext i
  simp [barVector, Matrix.mulVec, dotProduct, map_sum]

def conjugateHomCoordinates (n : ℕ) :
    (Layers.conjugate (ModuleCat.of (Laurent K D) (Term (Laurent K D) D n)) ⟶
      ModuleCat.of (Laurent K D) (Laurent K D)) ≃ₗ[Laurent K D]
        Module.Dual (Laurent K D) (Term (Laurent K D) D n) :=
  ModuleCat.homLinearEquiv.trans (conjugateCellEquiv K n).symm.dualMap

theorem conjugateHomCoordinates_precomp (n : ℕ) (w : Fin D → Laurent K D)
    (f : Layers.conjugate (ModuleCat.of (Laurent K D) (Term (Laurent K D) D n)) ⟶
      ModuleCat.of (Laurent K D) (Laurent K D)) :
    conjugateHomCoordinates K (n + 1)
      ((ModuleCat.restrictScalars (bar : Laurent K D ≃+* Laurent K D).toRingHom).map
        (boundary (Laurent K D) w n) ≫ f) =
      (boundary (Laurent K D) (fun i => bar (w i)) n).hom.dualMap
        (conjugateHomCoordinates K n f) := by
  apply LinearMap.ext
  intro v
  change f (boundary (Laurent K D) w n
    (show Term (Laurent K D) D (n + 1) from (conjugateCellEquiv K (n + 1)).symm v)) =
      f ((conjugateCellEquiv K n).symm
        (boundary (Laurent K D) (fun i => bar (w i)) n v))
  apply congrArg f
  apply (conjugateCellEquiv K n).injective
  rw [conjugateCellEquiv_boundary, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end
end Decoupling.HighDim.Toric
