import Decoupling.HighDim.ProfileStabilityPi
import Decoupling.HighDim.ToricStackMatrices
import Decoupling.HighDim.ToricNativeProfile
import Mathlib.LinearAlgebra.Quotient.Pi

/-!
# The native profile of the actual matrix-defined toric stack

Dependency of the necessity directions in new Corollaries 2 and 3. The
reduced module is the actual quotient by the dagger check matrix, and is
identified with the finite product of the individual reduced modules.
Full positive derived Hom then preserves this finite decomposition.
-/

namespace Decoupling.HighDim.Toric

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Matrix
noncomputable section
attribute [local instance] Classical.propDecidable HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (D : ℕ) {ι : Type} [Fintype ι]
  {rows cols : ι → ℕ}
  (B : ∀ i, Matrix (Fin (rows i)) (Fin (cols i)) (Laurent K D))

theorem stackMatrixReduced_range :
    (LinearMap.range (dagger (stackMatrix K D B)).mulVecLin).map
      (flattenCoordinates K D cols).symm.toLinearMap =
    Submodule.pi Set.univ (fun i => LinearMap.range (dagger (B i)).mulVecLin) := by
  ext v
  constructor
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    simp only [Submodule.mem_pi, Set.mem_univ, forall_const, LinearMap.mem_range]
    intro i
    refine ⟨(flattenCoordinates K D rows).symm z i, ?_⟩
    rw [stackMatrix_dagger]
    exact (stackMatrix_apply K D (fun i => dagger (B i)) z i).symm
  · intro hv
    have hi : ∀ i, ∃ z, dagger (B i) *ᵥ z = v i := by
      simpa only [Submodule.mem_pi, Set.mem_univ, forall_const, LinearMap.mem_range,
        Matrix.mulVecLin_apply] using hv
    choose z hz using hi
    refine ⟨dagger (stackMatrix K D B) *ᵥ flattenCoordinates K D rows z,
      ⟨flattenCoordinates K D rows z, rfl⟩, ?_⟩
    funext i
    rw [stackMatrix_dagger]
    exact (stackMatrix_apply K D (fun i => dagger (B i))
      (flattenCoordinates K D rows z) i).trans (by
        rw [LinearEquiv.symm_apply_apply]
        exact hz i)

/-- Coordinate change and quotient-of-products identify the actual reduced module. -/
def stackMatrixReducedEquiv : ProfileStability.matrixReduced (stackMatrix K D B) ≃ₗ[Laurent K D]
    (∀ i, ProfileStability.matrixReduced (B i)) :=
  (Submodule.Quotient.equiv _ _ (flattenCoordinates K D cols).symm
    (stackMatrixReduced_range K D B)).trans (Submodule.quotientPi
      (fun i => LinearMap.range (dagger (B i)).mulVecLin))

def stackMatrix_nativeProfileIso :
    ProfileStability.matrixProfile (stackMatrix K D B) ≅
      ⨁ fun i => ProfileStability.matrixProfile (B i) :=
  ProfileStability.moduleProfileIso (stackMatrixReducedEquiv K D B).toModuleIso ≪≫
    ProfileStability.modulePiProfileIso (fun i => ProfileStability.matrixReduced (B i))

variable (forms : ι → ℕ)

/-- Actual stack checks have the stated split native profile. The range
condition allows the empty stack and every internal toric form. -/
def stackChecks_nativeProfileIso (hforms : ∀ i, forms i + 1 ≤ D) :
    Profile.S_X (stackChecks K D forms) ≅ splitTarget K D forms := by
  change ProfileStability.matrixProfile (stackBoundaryMatrix K D forms 0) ≅ _
  rw [stackBoundaryMatrix_eq_stackMatrix]
  exact stackMatrix_nativeProfileIso K D (fun i => boundaryMatrix K D (forms i + 0)) ≪≫
    biproduct.mapIso (fun i => checks_nativeProfileIso K D (forms i) (D - (forms i + 1))
      (by have h := hforms i; omega))

end
end Decoupling.HighDim.Toric
