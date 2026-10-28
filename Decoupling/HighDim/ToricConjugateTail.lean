import Decoupling.HighDim.ToricTailCokernel
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings

/-!
# The explicit native resolution of the conjugated toric reduced module

Conjugation is the actual restriction-of-scalars equivalence along the
Laurent antipode. This module gives the finite-term resolution which the
independent native toric-profile calculation can dualize.
-/

namespace Decoupling.HighDim.Toric

open CategoryTheory Koszul

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [CommRing K] {D a k : ℕ}

def conjugateCellEquiv (n : ℕ) :
    Layers.conjugate (ModuleCat.of (Laurent K D) (Term (Laurent K D) D n)) ≃ₗ[Laurent K D]
      Term (Laurent K D) D n where
  toFun v := Finsupp.mapRange bar (by simp) v
  invFun v := Finsupp.mapRange bar (by simp) v
  left_inv v := by apply Finsupp.ext; intro I; simp
  right_inv v := by apply Finsupp.ext; intro I; simp
  map_add' v w := by
    apply Finsupp.ext
    intro I
    change bar ((show Term (Laurent K D) D n from v) I +
      (show Term (Laurent K D) D n from w) I) = _
    exact bar_add _ _
  map_smul' r v := by
    apply Finsupp.ext
    intro I
    change bar (bar r * (show Term (Laurent K D) D n from v) I) =
      r * bar ((show Term (Laurent K D) D n from v) I)
    simp

@[simp] theorem conjugateCellEquiv_apply (n : ℕ)
    (v : Layers.conjugate (ModuleCat.of (Laurent K D) (Term (Laurent K D) D n))) (I : Cell D n) :
    conjugateCellEquiv K n v I = bar ((show Term (Laurent K D) D n from v) I) := rfl

@[simp] theorem conjugateCellEquiv_symm_apply (n : ℕ)
    (v : Term (Laurent K D) D n) (I : Cell D n) :
    (show Term (Laurent K D) D n from (conjugateCellEquiv K n).symm v) I = bar (v I) := rfl

variable [IsDomain K]

def conjugateReducedResolution (h : a + (k + 1) = D) :
    ProjectiveResolution (Layers.conjugate (Layers.reduced (checks K D k))) :=
  (ModuleCat.restrictScalars (bar : Laurent K D ≃+* Laurent K D).toRingHom).mapProjectiveResolution
    (reducedResolution K h)

instance conjugateReducedResolution_finite (h : a + (k + 1) = D) (n : ℕ) :
    Module.Finite (Laurent K D) ((conjugateReducedResolution K h).complex.X n) := by
  let : Module.Finite (Laurent K D) (Laurent K D) := Module.Finite.self _
  exact Module.Finite.equiv (conjugateCellEquiv K (a + n)).symm

instance conjugateReducedResolution_free (h : a + (k + 1) = D) (n : ℕ) :
    Module.Free (Laurent K D) ((conjugateReducedResolution K h).complex.X n) :=
  Module.Free.of_equiv (conjugateCellEquiv K (a + n)).symm

def nativeProfileIso (h : a + (k + 1) = D) :
    Profile.ofResolution (conjugateReducedResolution K h)
      (ModuleCat.of (Laurent K D) (Laurent K D)) ≅ Profile.S_X (checks K D k) :=
  ResolutionComparison.profileIso _ (conjugateReducedResolution K h) (Profile.resolution (checks K D k))

end
end Decoupling.HighDim.Toric
