import Decoupling.HighDim.TorusBaseChange

/-!
# The periodic logical quotient is homology of the actual tensor model

Source: Appendix B.3. We identify the physical three-term window of the
bounded finite free CSS complex, extend its scalars to the genuine period
group algebra, and recover precisely the periodic check matrices. Thus the
logical quotient is linked to a real base-changed complex, independently
of any splitting or profile-count definition.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits Matrix FiniteResolution
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {K : Type} [Field K] {D q s r : ℕ}

/-- Original physical window over the Laurent ring. -/
def checkWindow (c : CSS.Checks K D q s r) (hc : c.Topological) :
    ShortComplex (ModuleCat (Laurent K D)) :=
  ShortComplex.moduleCatMk (dagger c.H_Z).mulVecLin c.H_X.mulVecLin (by
    apply LinearMap.ext
    intro v
    funext i
    change (c.H_X *ᵥ (dagger c.H_Z *ᵥ v)) i = 0
    rw [Matrix.mulVec_mulVec, c.checks_commute hc]
    simp)

/-- The finite free model really retains both given checks in degrees
minus one, zero, and one. -/
def cssWindowIso (c : CSS.Checks K D q s r) (hc : c.Topological) :
    (cssComplex c hc).sc' (-1) 0 1 ≅ checkWindow c hc :=
  ShortComplex.isoMk (Iso.refl _)
    (cssDualZeroCoordinates c).toModuleIso (cssDualOneCoordinates c).toModuleIso
    (by ext v; exact (connectingMap_coordinates c v).symm)
    (by ext v; exact (cssDual_d_zero_one c v).symm)

/-- Periodic physical window, before forgetting to the coefficient field. -/
def periodicWindow (L : AddSubgroup (Translation D)) (c : CSS.Checks K D q s r)
    (hc : c.Topological) : ShortComplex (ModuleCat (PeriodRing K L)) :=
  ShortComplex.moduleCatMk ((dagger c.H_Z).map (periodMap L)).mulVecLin
    (c.H_X.map (periodMap L)).mulVecLin (by
      apply LinearMap.ext
      intro v
      funext i
      change ((c.H_X.map (periodMap L)) *ᵥ ((dagger c.H_Z).map (periodMap L) *ᵥ v)) i = 0
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, c.checks_commute hc]
      simp)

/-- The physical periodic matrices are obtained by genuine tensor-product
extension of the original window. -/
def extensionWindowIso (L : AddSubgroup (Translation D)) (c : CSS.Checks K D q s r)
    (hc : c.Topological) :
    (checkWindow c hc).map (ModuleCat.extendScalars (periodMap L)) ≅ periodicWindow L c hc :=
  ShortComplex.isoMk (extensionFreeIso (periodMap L) r)
    (extensionFreeIso (periodMap L) q) (extensionFreeIso (periodMap L) s)
    (extensionFreeIso_naturality _ (dagger c.H_Z)).symm
    (extensionFreeIso_naturality _ c.H_X).symm

/-- Coefficients embed as constant group-algebra elements on the torus. -/
def periodConstant (L : AddSubgroup (Translation D)) : K →+* PeriodRing K L :=
  AddMonoidAlgebra.singleZeroRingHom

/-- Forget the actual period-ring scalars while retaining the field action. -/
abbrev periodCoefficients (L : AddSubgroup (Translation D)) :
    ModuleCat (PeriodRing K L) ⥤ ModuleCat K := ModuleCat.restrictScalars (periodConstant L)

/-- The two standard presentations of coefficient scalar action coincide. -/
def periodFreeCoefficientsIso (L : AddSubgroup (Translation D)) (n : ℕ) :
    (periodCoefficients (K := K) L).obj (ModuleCat.of (PeriodRing K L) (Fin n → PeriodRing K L)) ≅
      ModuleCat.of K (Fin n → PeriodRing K L) := by
  let e : (periodCoefficients (K := K) L).obj
      (ModuleCat.of (PeriodRing K L) (Fin n → PeriodRing K L)) ≃ₗ[K]
        (Fin n → PeriodRing K L) := {
    toFun := fun v => v
    invFun := fun v => v
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
    map_add' := fun _ _ => rfl
    map_smul' := fun a v => by
      funext i
      change AddMonoidAlgebra.single 0 a * (show Fin n → PeriodRing K L from v) i =
        a • (show Fin n → PeriodRing K L from v) i
      apply AddMonoidAlgebra.coeff_injective
      ext t
      simp }
  exact e.toModuleIso

/-- Coefficient restriction recovers precisely `ker/image` input maps. -/
def periodicWindowFieldIso (L : AddSubgroup (Translation D))
    (c : CSS.Checks K D q s r) (hc : c.Topological) :
    (periodicWindow L c hc).map (periodCoefficients L) ≅ periodicSc L c hc :=
  ShortComplex.isoMk (periodFreeCoefficientsIso L r)
    (periodFreeCoefficientsIso L q) (periodFreeCoefficientsIso L s)
    (by ext v; rfl) (by ext v; rfl)

end
end Decoupling.HighDim.Torus
