import Decoupling.HighDim.FiniteResolutionCSS

/-!
# Coordinates of the conjugate dual and the physical check map

The first two terms of the actual finite conjugate-dual resolution are
identified with the original finite Pauli/check coordinate modules.
Conjugating the resolution before dualizing is essential: precomposition
then gives the dagger, with the antipode and transpose both retained.
-/

namespace Decoupling.HighDim.FiniteResolution

open CategoryTheory Matrix

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] {D : ℕ}

def conjugateFreeBasis (n : ℕ) : Module.Basis (Fin n) (Laurent K D)
    (Layers.conjugate (ModuleCat.of (Laurent K D) (CSS.Free K D n))) :=
  (Pi.basisFun (Laurent K D) (Fin n)).map (Layers.conjugateFreeEquiv (Fin n)).symm

/-- Coordinates of genuine Hom from the conjugated finite free module. -/
def dualFreeCoordinates (n : ℕ) :
    (Layers.conjugate (ModuleCat.of (Laurent K D) (CSS.Free K D n)) ⟶
      ModuleCat.of (Laurent K D) (Laurent K D)) ≃ₗ[Laurent K D] CSS.Free K D n :=
  ModuleCat.homLinearEquiv.trans ((conjugateFreeBasis n).constr (Laurent K D)).symm

theorem dualFreeCoordinates_apply (n : ℕ)
    (g : Layers.conjugate (ModuleCat.of (Laurent K D) (CSS.Free K D n)) ⟶
      ModuleCat.of (Laurent K D) (Laurent K D)) (i : Fin n) :
    dualFreeCoordinates n g i = g (conjugateFreeBasis n i) := rfl

theorem conjugateFreeBasis_repr (n : ℕ)
    (a : Layers.conjugate (ModuleCat.of (Laurent K D) (CSS.Free K D n))) (i : Fin n) :
    (conjugateFreeBasis n).repr a i = bar (a i) := by
  simp [conjugateFreeBasis, Layers.conjugateFreeEquiv]

theorem dualFreeCoordinates_evaluate (n : ℕ)
    (g : Layers.conjugate (ModuleCat.of (Laurent K D) (CSS.Free K D n)) ⟶
      ModuleCat.of (Laurent K D) (Laurent K D))
    (a : Layers.conjugate (ModuleCat.of (Laurent K D) (CSS.Free K D n))) :
    g a = ∑ i, bar (a i) * dualFreeCoordinates n g i := by
  have h := congrArg (fun z => g z) ((conjugateFreeBasis n).sum_repr a)
  simpa only [map_sum, map_smul, smul_eq_mul, conjugateFreeBasis_repr,
    dualFreeCoordinates_apply] using h.symm

/-- Restricting the matrix map along the antipode is the conjugated map. -/
def conjugateMatrixMap {m n : ℕ} (A : Matrix (Fin m) (Fin n) (Laurent K D)) :
    Layers.conjugate (ModuleCat.of (Laurent K D) (CSS.Free K D n)) ⟶
      Layers.conjugate (ModuleCat.of (Laurent K D) (CSS.Free K D m)) :=
  (ModuleCat.restrictScalars (bar : Laurent K D ≃+* Laurent K D).toRingHom).map
    (ModuleCat.ofHom A.mulVecLin)

theorem dualFreeCoordinates_precomp {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (Laurent K D))
    (g : Layers.conjugate (ModuleCat.of (Laurent K D) (CSS.Free K D m)) ⟶
      ModuleCat.of (Laurent K D) (Laurent K D)) :
    dualFreeCoordinates n (conjugateMatrixMap A ≫ g) =
      dagger A *ᵥ dualFreeCoordinates m g := by
  funext i
  rw [dualFreeCoordinates_apply]
  change g (A *ᵥ (conjugateFreeBasis n i)) = _
  rw [dualFreeCoordinates_evaluate]
  simp [conjugateFreeBasis, Layers.conjugateFreeEquiv, dagger,
    Matrix.mulVec, dotProduct, Pi.basisFun_apply, Pi.single_apply]

variable {q s r : ℕ}

/-- Degree zero of the actual dual resolution has the original Pauli coordinates. -/
def cssDualZeroCoordinates (c : CSS.Checks K D q s r) :
    (cssDual c).X 0 ≃ₗ[Laurent K D] CSS.Free K D q := dualFreeCoordinates q

/-- Degree one of the actual dual resolution has the original check coordinates. -/
def cssDualOneCoordinates (c : CSS.Checks K D q s r) :
    (cssDual c).X 1 ≃ₗ[Laurent K D] CSS.Free K D s := dualFreeCoordinates s

/-- In these actual coordinates the differential is precisely `H_X`. -/
theorem cssDual_d_zero_one (c : CSS.Checks K D q s r) (g : (cssDual c).X 0) :
    cssDualOneCoordinates c ((cssDual c).d 0 1 g) =
      c.H_X *ᵥ cssDualZeroCoordinates c g := by
  change dualFreeCoordinates s
    ((cssConjugateResolution c).complex.d 1 0 ≫ g) = _
  change dualFreeCoordinates s (conjugateMatrixMap (dagger c.H_X) ≫ g) = _
  rw [dualFreeCoordinates_precomp, dagger_dagger]
  rfl

end

end Decoupling.HighDim.FiniteResolution
