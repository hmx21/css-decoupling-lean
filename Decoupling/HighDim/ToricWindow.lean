import Decoupling.HighDim.ToricModel
import Decoupling.HighDim.CSS

/-!
# The actual toric check matrices in the physical window

The finite coordinates here are obtained by enumerating the actual
ordered coordinate cells. The matrices are the signed Koszul boundaries,
with `H_Z` the dagger of the upper boundary. No exactness certificate is
an input. The X-side exactness is proved here; the dual-side exactness
and the dual-lattice identification require the separate Hodge argument.
-/

namespace Decoupling.HighDim.Toric

open CategoryTheory Matrix

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [CommRing K] (D : ℕ)

abbrev cellCount (k : ℕ) : ℕ := Fintype.card (Koszul.Cell D k)

/-- Enumeration changes only the labels of the actual ordered cells. -/
def cellCoordinates (k : ℕ) : Koszul.Term (Laurent K D) D k ≃ₗ[Laurent K D]
    CSS.Free K D (cellCount D k) :=
  (Finsupp.domLCongr (R := Laurent K D) (M := Laurent K D)
    (Fintype.equivFin (Koszul.Cell D k))).trans
      (Finsupp.linearEquivFunOnFinite (Laurent K D) (Laurent K D) _)

def boundaryMatrix (k : ℕ) :
    Matrix (Fin (cellCount D k)) (Fin (cellCount D (k + 1))) (Laurent K D) :=
  LinearMap.toMatrix' ((cellCoordinates K D k).toLinearMap.comp
    ((Koszul.boundary (Laurent K D) (difference K) k).hom.comp
      (cellCoordinates K D (k + 1)).symm.toLinearMap))

theorem boundaryMatrix_apply (k : ℕ) (v : CSS.Free K D (cellCount D (k + 1))) :
    boundaryMatrix K D k *ᵥ v = cellCoordinates K D k
      (Koszul.boundary (Laurent K D) (difference K) k
        ((cellCoordinates K D (k + 1)).symm v)) :=
  LinearMap.toMatrix'_mulVec _ _

/-- `checks K D k` is the `(k+1)`-form toric code. The offset avoids
truncated subtraction at the lower boundary of the physical window. -/
def checks (k : ℕ) : CSS.Checks K D (cellCount D (k + 1))
    (cellCount D k) (cellCount D (k + 2)) where
  H_X := boundaryMatrix K D k
  H_Z := dagger (boundaryMatrix K D (k + 1))

@[simp] theorem checks_H_X (k : ℕ) : (checks K D k).H_X = boundaryMatrix K D k := rfl
@[simp] theorem checks_dagger_H_Z (k : ℕ) :
    dagger (checks K D k).H_Z = boundaryMatrix K D (k + 1) := dagger_dagger _

theorem checks_commute (k : ℕ) : (checks K D k).H_X * dagger (checks K D k).H_Z = 0 := by
  apply Matrix.mulVec_injective
  funext v
  rw [checks_H_X, checks_dagger_H_Z, ← Matrix.mulVec_mulVec,
    boundaryMatrix_apply, boundaryMatrix_apply, LinearEquiv.symm_apply_apply]
  have h := congrArg (fun f => f ((cellCoordinates K D (k + 2)).symm v))
    (Koszul.boundary_squared (Laurent K D) (difference K) k)
  simpa using congrArg (cellCoordinates K D k) h

variable [IsDomain K]

theorem checks_exact_X (k : ℕ) : LinearMap.ker (checks K D k).H_X.mulVecLin =
    LinearMap.range (dagger (checks K D k).H_Z).mulVecLin := by
  ext x
  change (checks K D k).H_X *ᵥ x = 0 ↔
    ∃ z, dagger (checks K D k).H_Z *ᵥ z = x
  rw [checks_H_X, checks_dagger_H_Z]
  constructor
  · intro hx
    rw [boundaryMatrix_apply] at hx
    have hx' : Koszul.boundary (Laurent K D) (difference K) k
        ((cellCoordinates K D (k + 1)).symm x) = 0 :=
      (cellCoordinates K D k).map_eq_zero_iff.mp hx
    obtain ⟨z, hz⟩ := Koszul.laurent_exact K D k _ hx'
    refine ⟨cellCoordinates K D (k + 2) z, ?_⟩
    rw [boundaryMatrix_apply, LinearEquiv.symm_apply_apply, hz,
      LinearEquiv.apply_symm_apply]
  · rintro ⟨z, rfl⟩
    rw [Matrix.mulVec_mulVec, ← checks_H_X K D k, ← checks_dagger_H_Z K D k,
      checks_commute, Matrix.zero_mulVec]

end
end Decoupling.HighDim.Toric
