import Decoupling.HighDim.ToricTailResolution
import Decoupling.HighDim.ToricDualLatticeTransport
import Decoupling.HighDim.ResolutionComparison

/-!
# The native Koszul tail resolves the actual toric reduced module

The identification uses the actual signed monomial Hodge matrix and
its proved commuting square, and then transports the augmentation.
-/

namespace Decoupling.HighDim.Toric

open CategoryTheory Matrix Koszul

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [CommRing K] (D a : ℕ)

theorem tail_range_coordinates :
    (LinearMap.range ((tailComplex K D a).d 1 0).hom).map
      (cellCoordinates K D a).toLinearMap = LinearMap.range (boundaryMatrix K D a).mulVecLin := by
  change (LinearMap.range ((laurentComplex K D).d (a + 1) a).hom).map _ = _
  simp only [laurentComplex, complex_d]
  ext x
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    refine ⟨cellCoordinates K D (a + 1) y, ?_⟩
    change boundaryMatrix K D a *ᵥ cellCoordinates K D (a + 1) y = _
    rw [boundaryMatrix_apply, LinearEquiv.symm_apply_apply]
    rfl
  · rintro ⟨y, rfl⟩
    refine ⟨boundary (Laurent K D) (difference K) a ((cellCoordinates K D (a + 1)).symm y),
      ⟨(cellCoordinates K D (a + 1)).symm y, rfl⟩, ?_⟩
    exact (boundaryMatrix_apply K D a y).symm

def tailCokernelCoordinates : TailCokernel K D a ≃ₗ[Laurent K D] (checks K D a).CheckCokernel :=
  Submodule.Quotient.equiv _ _ (cellCoordinates K D a) (tail_range_coordinates K D a)

variable {D a} {k : ℕ}

theorem complementary_range (h : a + (k + 1) = D) :
    (LinearMap.range (boundaryMatrix K D a).mulVecLin).map
      (dualLatticeCoordinates K h).toLinearMap =
        LinearMap.range (dagger (boundaryMatrix K D k)).mulVecLin := by
  have hd := dualLatticeMatrix_boundary K (by omega : a + 1 + k = D)
  ext x
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    refine ⟨dualLatticeCoordinates K (by omega : (a + 1) + k = D) y, ?_⟩
    change dagger (boundaryMatrix K D k) *ᵥ _ = dualLatticeCoordinates K h (boundaryMatrix K D a *ᵥ y)
    rw [← dualLatticeMatrix_mulVec, ← dualLatticeMatrix_mulVec,
      Matrix.mulVec_mulVec, ← hd, ← Matrix.mulVec_mulVec, dualLatticeMatrix_mulVec]
  · rintro ⟨y, rfl⟩
    let z := (dualLatticeCoordinates K (by omega : (a + 1) + k = D)).symm y
    refine ⟨boundaryMatrix K D a *ᵥ z, ⟨z, rfl⟩, ?_⟩
    change dualLatticeCoordinates K h (boundaryMatrix K D a *ᵥ z) = _
    rw [← dualLatticeMatrix_mulVec, Matrix.mulVec_mulVec, hd,
      ← Matrix.mulVec_mulVec, dualLatticeMatrix_mulVec]
    simp only [z, LinearEquiv.apply_symm_apply]
    rfl

/-- Complementary-tail cokernel equals `coker H_X†`, not the check cokernel. -/
def complementaryReducedEquiv (h : a + (k + 1) = D) :
    TailCokernel K D a ≃ₗ[Laurent K D] (checks K D k).M_X :=
  (tailCokernelCoordinates K D a).trans
    (Submodule.Quotient.equiv _ _ (dualLatticeCoordinates K h) (complementary_range K h))

variable [IsDomain K]

/-- The augmentation is transported through the proved actual quotient
isomorphism. Every term and differential remain the explicit Koszul tail. -/
def reducedResolution (h : a + (k + 1) = D) :
    ProjectiveResolution (ModuleCat.of (Laurent K D) (checks K D k).M_X) :=
  ResolutionComparison.transportResolution (tailResolution K D a)
    (complementaryReducedEquiv K h).toModuleIso

end
end Decoupling.HighDim.Toric
