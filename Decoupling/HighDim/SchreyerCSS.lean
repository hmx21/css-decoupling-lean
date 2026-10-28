import Decoupling.HighDim.SchreyerPrefix
import Decoupling.HighDim.FiniteResolutionDual
import Decoupling.HighDim.FiniteResolutionConnected

/-!
# HD014 native CSS resolution with its prescribed three-term prefix

`Input` is the intermediate consumer contract for the actual Laurent
Schreyer tails. The final existence theorem must construct those tails
internally. This file builds the actual native resolution and conjugate
dual and proves their coordinates. Freeness is transported from explicit
finite powers, including through antipode conjugation; it never uses
`FiniteResolution.Data.free` or finite-projective-freeness.
-/
namespace Decoupling.HighDim.SchreyerCSS
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Matrix
open SchreyerLocalization
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
variable {K : Type} [Field K] {D q s r : ℕ}

structure Input (c : CSS.Checks K D q s r) where
  t : ℕ
  gamma : Matrix (Fin t) (Fin s) (Laurent K D)
  exact_gamma : LinearMap.range (dagger gamma).mulVecLin =
    LinearMap.ker (dagger c.H_X).mulVecLin
  positive : FreeData (FiniteResolution.Syzygy
    (ModuleCat.ofHom (dagger gamma).mulVecLin)) (D - 1)
  negative : FreeData (FiniteResolution.Syzygy (FiniteResolution.zCover c)) (D - 1)

variable (c : CSS.Checks K D q s r) (A : Input c)

/-- Actual finite free resolution retaining all three specified modules. -/
def freeData : FreeData (Layers.reduced c) (D - 1 + 3) :=
  SchreyerPrefix.freeData (FiniteResolution.cssPresentation c)
    (ModuleCat.ofHom (dagger A.gamma).mulVecLin) A.exact_gamma A.positive
    (LinearEquiv.refl _ _) (LinearEquiv.refl _ _) (LinearEquiv.refl _ _)

def resolution : ProjectiveResolution (Layers.reduced c) :=
  (freeData c A).data.toProjectiveResolution

@[simp] theorem resolution_X_zero : (resolution c A).complex.X 0 =
    ModuleCat.of (Laurent K D) (CSS.Free K D q) := rfl
@[simp] theorem resolution_X_one : (resolution c A).complex.X 1 =
    ModuleCat.of (Laurent K D) (CSS.Free K D s) := rfl
@[simp] theorem resolution_X_two : (resolution c A).complex.X 2 =
    ModuleCat.of (Laurent K D) (CSS.Free K D A.t) := rfl

@[simp] theorem resolution_d_one_zero :
    (resolution c A).complex.d 1 0 = FiniteResolution.cssPresentation c :=
  (freeData c A).data.complex_d 0
@[simp] theorem resolution_d_two_one :
    (resolution c A).complex.d 2 1 = ModuleCat.ofHom (dagger A.gamma).mulVecLin :=
  (freeData c A).data.complex_d 1

instance resolution_finite (k : ℕ) :
    Module.Finite (Laurent K D) ((resolution c A).complex.X k) :=
  (freeData c A).data.finite k
instance resolution_free (k : ℕ) :
    Module.Free (Laurent K D) ((resolution c A).complex.X k) :=
  (freeData c A).free k

def conjugateResolution : ProjectiveResolution (Layers.conjugate (Layers.reduced c)) :=
  (ModuleCat.restrictScalars (bar : Laurent K D ≃+* Laurent K D).toRingHom).mapProjectiveResolution
    (resolution c A)

/-- Transport the already constructed coordinates through the actual antipode. -/
def conjugateCoordinates (k : ℕ) :
    (conjugateResolution c A).complex.X k ≃ₗ[Laurent K D]
      (Fin ((freeData c A).rank k) → Laurent K D) :=
  ((ModuleCat.restrictScalars (bar : Laurent K D ≃+* Laurent K D).toRingHom).mapIso
    ((freeData c A).coordinates k).toModuleIso).toLinearEquiv.trans
      (Layers.conjugateFreeEquiv (Fin ((freeData c A).rank k)))

instance conjugateResolution_finite (k : ℕ) :
    Module.Finite (Laurent K D) ((conjugateResolution c A).complex.X k) := by
  let : Module.Finite (Laurent K D) (Fin ((freeData c A).rank k) → Laurent K D) :=
    Module.Finite.of_basis (Pi.basisFun (Laurent K D) _)
  exact Module.Finite.equiv (conjugateCoordinates c A k).symm
instance conjugateResolution_free (k : ℕ) :
    Module.Free (Laurent K D) ((conjugateResolution c A).complex.X k) :=
  Module.Free.of_equiv (conjugateCoordinates c A k).symm

theorem conjugateResolution_zero_above (hD : 1 ≤ D) (k : ℕ) (hk : D+2<k) :
    IsZero ((conjugateResolution c A).complex.X k) :=
  (ModuleCat.restrictScalars (bar : Laurent K D ≃+* Laurent K D).toRingHom).map_isZero
    ((freeData c A).data.zero_above k (by omega))

def dual : CochainComplex (ModuleCat (Laurent K D)) ℕ :=
  ResolutionCohomology.dualComplex (conjugateResolution c A)
    (ModuleCat.of (Laurent K D) (Laurent K D))

instance dual_finite (k : ℕ) : Module.Finite (Laurent K D) ((dual c A).X k) := by
  let : Module.Finite (Laurent K D) (Laurent K D) := Module.Finite.self _
  let := conjugateResolution_finite c A k
  let := conjugateResolution_free c A k
  change Module.Finite (Laurent K D)
    ((conjugateResolution c A).complex.X k ⟶ ModuleCat.of (Laurent K D) (Laurent K D))
  exact Module.Finite.equiv ModuleCat.homLinearEquiv.symm
instance dual_free (k : ℕ) : Module.Free (Laurent K D) ((dual c A).X k) := by
  change Module.Free (Laurent K D)
    ((conjugateResolution c A).complex.X k ⟶ ModuleCat.of (Laurent K D) (Laurent K D))
  exact Module.Free.of_equiv ModuleCat.homLinearEquiv.symm

theorem dual_zero_above (hD : 1 ≤ D) (k : ℕ) (hk : D+2<k) : IsZero ((dual c A).X k) := by
  let : Subsingleton
      ((conjugateResolution c A).complex.X k ⟶ ModuleCat.of (Laurent K D) (Laurent K D)) :=
    ⟨fun f g => (conjugateResolution_zero_above c A hD k hk).eq_of_src f g⟩
  change IsZero (ModuleCat.of (Laurent K D)
    ((conjugateResolution c A).complex.X k ⟶ ModuleCat.of (Laurent K D) (Laurent K D)))
  exact ModuleCat.isZero_of_subsingleton _

def zeroCoordinates : (dual c A).X 0 ≃ₗ[Laurent K D] CSS.Free K D q :=
  FiniteResolution.dualFreeCoordinates q

def oneCoordinates : (dual c A).X 1 ≃ₗ[Laurent K D] CSS.Free K D s :=
  FiniteResolution.dualFreeCoordinates s

def twoCoordinates : (dual c A).X 2 ≃ₗ[Laurent K D] CSS.Free K D A.t :=
  FiniteResolution.dualFreeCoordinates A.t

theorem dual_d_zero_one (x : (dual c A).X 0) :
    oneCoordinates c A ((dual c A).d 0 1 x) = c.H_X *ᵥ zeroCoordinates c A x := by
  change FiniteResolution.dualFreeCoordinates s
    (FiniteResolution.conjugateMatrixMap (dagger c.H_X) ≫ x) = _
  rw [FiniteResolution.dualFreeCoordinates_precomp,dagger_dagger]
  rfl

theorem dual_d_one_two (x : (dual c A).X 1) :
    twoCoordinates c A ((dual c A).d 1 2 x) = A.gamma *ᵥ oneCoordinates c A x := by
  change FiniteResolution.dualFreeCoordinates A.t
    (FiniteResolution.conjugateMatrixMap (dagger A.gamma) ≫ x) = _
  rw [FiniteResolution.dualFreeCoordinates_precomp,dagger_dagger]
  rfl

/-- Negative-side resolution, preserving the original Z-check module. -/
def zFreeData : FreeData (FiniteResolution.zImage c) (D - 1 + 1) :=
  SchreyerPrefix.prepend (FiniteResolution.zCover c) (FiniteResolution.zCover_surjective c)
    (LinearEquiv.refl _ _) A.negative

end
end Decoupling.HighDim.SchreyerCSS
