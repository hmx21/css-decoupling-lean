import Decoupling.HighDim.ToricStack
import Decoupling.HighDim.FiniteResolutionCokernel

/-!
# Actual CSS matrices for a finite toric stack

The Pauli and check coordinates enumerate pairs consisting of a copy and
one of its actual ordered cells. The differential is the direct sum of
the oriented Koszul boundaries. Theorems below identify its actual check
cokernel and remove all auxiliary model inputs from the split-profile
comparison, including the empty-stack case.
-/

namespace Decoupling.HighDim.Toric

open CategoryTheory CategoryTheory.Limits HomologicalComplex Matrix

noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [Field K] (D : ℕ) {ι : Type} [Fintype ι] (forms : ι → ℕ)

abbrev stackCount (offset : ℕ) : ℕ :=
  Fintype.card (Σ i : ι, Fin (cellCount D (forms i + offset)))

def flattenCoordinates (counts : ι → ℕ) :
    (∀ i, Fin (counts i) → Laurent K D) ≃ₗ[Laurent K D]
      (Fin (Fintype.card (Σ i, Fin (counts i))) → Laurent K D) :=
  (LinearEquiv.piCurry (Laurent K D) (fun i (_ : Fin (counts i)) => Laurent K D)).symm.trans
    (LinearEquiv.piCongrLeft' (Laurent K D) (fun _ : Σ i, Fin (counts i) => Laurent K D)
      (Fintype.equivFin _))

/-- Offset `0,1,2` gives respectively degrees `1,0,-1`. -/
def stackCoordinates (offset : ℕ) :
    (stackModel K D forms).X (1 - offset) ≃ₗ[Laurent K D]
      CSS.Free K D (stackCount D forms offset) :=
  (stackTermIso K D forms (1 - offset)).toLinearEquiv.trans
    ((LinearEquiv.piCongrRight (fun i =>
      ((Koszul.laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE (forms i + 1))
        (i := forms i + offset) (i' := 1 - offset) (by simp)).toLinearEquiv.trans
          (cellCoordinates K D (forms i + offset)))).trans
      (flattenCoordinates K D (fun i => cellCount D (forms i + offset))))

def stackBoundaryMatrix (offset : ℕ) :
    Matrix (Fin (stackCount D forms offset)) (Fin (stackCount D forms (offset + 1)))
      (Laurent K D) :=
  LinearMap.toMatrix' ((stackCoordinates K D forms offset).toLinearMap.comp
    (((stackModel K D forms).d (1 - (offset + 1 : ℕ)) (1 - offset)).hom.comp
      (stackCoordinates K D forms (offset + 1)).symm.toLinearMap))

theorem stackBoundaryMatrix_apply (offset : ℕ)
    (v : CSS.Free K D (stackCount D forms (offset + 1))) :
    stackBoundaryMatrix K D forms offset *ᵥ v = stackCoordinates K D forms offset
      ((stackModel K D forms).d (1 - (offset + 1 : ℕ)) (1 - offset)
        ((stackCoordinates K D forms (offset + 1)).symm v)) :=
  LinearMap.toMatrix'_mulVec _ _

def stackChecks : CSS.Checks K D (stackCount D forms 1) (stackCount D forms 0)
    (stackCount D forms 2) where
  H_X := stackBoundaryMatrix K D forms 0
  H_Z := dagger (stackBoundaryMatrix K D forms 1)

@[simp] theorem stackChecks_H_X : (stackChecks K D forms).H_X = stackBoundaryMatrix K D forms 0 := rfl
@[simp] theorem stackChecks_dagger_H_Z :
    dagger (stackChecks K D forms).H_Z = stackBoundaryMatrix K D forms 1 := dagger_dagger _

theorem stackChecks_exact_X (v : CSS.Free K D (stackCount D forms 1)) :
    (stackChecks K D forms).H_X *ᵥ v = 0 ↔
      ∃ z, dagger (stackChecks K D forms).H_Z *ᵥ z = v := by
  rw [stackChecks_H_X, stackChecks_dagger_H_Z]
  constructor
  · intro hv
    rw [stackBoundaryMatrix_apply] at hv
    have hzero := (stackCoordinates K D forms 0).map_eq_zero_iff.mp hv
    have he := stackModel_exact_zero K D forms
    rw [(stackModel K D forms).exactAt_iff' (-1) 0 1 (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff] at he
    obtain ⟨z, hz⟩ := he ((stackCoordinates K D forms 1).symm v) hzero
    change (stackModel K D forms).d (-1) 0 z = (stackCoordinates K D forms 1).symm v at hz
    refine ⟨stackCoordinates K D forms 2 z, ?_⟩
    rw [stackBoundaryMatrix_apply, LinearEquiv.symm_apply_apply]
    change stackCoordinates K D forms 1 ((stackModel K D forms).d (-1) 0 z) = v
    rw [hz, LinearEquiv.apply_symm_apply]
  · rintro ⟨z, rfl⟩
    rw [stackBoundaryMatrix_apply, stackBoundaryMatrix_apply, LinearEquiv.symm_apply_apply]
    have hh := congrArg (fun f => f ((stackCoordinates K D forms 2).symm z))
      ((stackModel K D forms).d_comp_d (1 - (2 : ℕ)) (1 - (1 : ℕ)) (1 - (0 : ℕ)))
    exact (congrArg (stackCoordinates K D forms 0) hh).trans (map_zero _)

theorem stackRange_coordinates :
    (LinearMap.range ((stackModel K D forms).d 0 1).hom).map
      (stackCoordinates K D forms 0).toLinearMap =
        LinearMap.range (stackChecks K D forms).H_X.mulVecLin := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    refine ⟨stackCoordinates K D forms 1 y, ?_⟩
    change stackBoundaryMatrix K D forms 0 *ᵥ _ = _
    rw [stackBoundaryMatrix_apply, LinearEquiv.symm_apply_apply]
    rfl
  · rintro ⟨y, rfl⟩
    refine ⟨(stackModel K D forms).d 0 1 ((stackCoordinates K D forms 1).symm y),
      ⟨(stackCoordinates K D forms 1).symm y, rfl⟩, ?_⟩
    exact (stackBoundaryMatrix_apply K D forms 0 y).symm

def stackCheckCokernelEquiv : CochainCokernel.CheckCokernel (stackModel K D forms)
    ≃ₗ[Laurent K D] (stackChecks K D forms).CheckCokernel :=
  Submodule.Quotient.equiv _ _ (stackCoordinates K D forms 0) (stackRange_coordinates K D forms)

/-- An actual split native profile gives the actual toric-stack stable
check-cokernel equivalence, with no model/exactness/freeness certificate input. -/
theorem stableCheckCokernel_of_split {q s r : ℕ} (c : CSS.Checks K D q s r)
    (hc : c.Topological) (e : Profile.S_X c ≅ splitTarget K D forms) :
    ∃ a b : ℕ, Nonempty
      (((stackChecks K D forms).CheckCokernel × (Fin b → Laurent K D)) ≃ₗ[Laurent K D]
        (c.CheckCokernel × (Fin a → Laurent K D))) := by
  obtain ⟨a, b, ⟨f⟩⟩ := stableCokernel_of_split K D forms c hc e
  exact ⟨a, b, ⟨((stackCheckCokernelEquiv K D forms).symm.prodCongr
    (LinearEquiv.refl _ _)).trans (f.trans
      ((FiniteResolution.cssComplex_checkCokernelEquiv c hc).prodCongr (LinearEquiv.refl _ _)))⟩⟩

end
end Decoupling.HighDim.Toric
