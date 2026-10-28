import Decoupling.HighDim.TorusKoszulDoubleDual
import Decoupling.HighDim.TorusRepresentable

/-!
# Derived local duality for bounded finite free complexes

The Koszul resolution, ordinary cochain duality, and the genuine
K-projective localization theorem give a linear equivalence from native
derived morphisms `F[-D] ⟶ C` to homotopy classes `C* ⟶ F`.
The remaining tensor interpretation is handled separately.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section General
variable {R : Type} [CommRing R]

/-- The actual localization map is a linear equivalence from a
K-projective source. -/
def homotopyDerivedEquiv (C E : CochainComplex (ModuleCat R) ℤ) [C.IsKProjective] :
    ((homotopyQuotient R).obj C ⟶ (homotopyQuotient R).obj E) ≃ₗ[R]
      (DerivedCategory.Q.obj C ⟶ DerivedCategory.Q.obj E) :=
  (LinearEquiv.ofBijective (DerivedCategory.Qh.mapLinearMap R)
    (CochainComplex.IsKProjective.Qh_map_bijective C ((homotopyQuotient R).obj E))).trans
      (CategoryTheory.Linear.homCongr R
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app C)
        ((DerivedCategory.quotientCompQhIso (ModuleCat R)).app E))

end General

variable (K : Type) [Field K] (D : ℕ)

/-- Finite-perfect local duality, obtained solely from actual cochain
duality and the proved Koszul self-duality. -/
def localDualityHomEquiv (C : CochainComplex (ModuleCat (Laurent K D)) ℤ)
    [∀ n, Module.Finite (Laurent K D) (C.X n)]
    [∀ n, Module.Free (Laurent K D) (C.X n)]
    (b : ℤ) [C.IsStrictlyGE b] :
    (probe K D ⟶ DerivedCategory.Q.obj C) ≃ₗ[Laurent K D]
      ((homotopyQuotient (Laurent K D)).obj (complexDual (Laurent K D) C) ⟶
        (homotopyQuotient (Laurent K D)).obj
          ((CochainComplex.singleFunctor (ModuleCat (Laurent K D)) 0).obj
            (Koszul.coefficientModule K D))) := by
  let : (complexDual (Laurent K D) C).IsKProjective :=
    CochainComplex.isKProjective_of_projective _ (-b)
  exact
    (CategoryTheory.Linear.homCongr (Laurent K D)
      (coefficientResolutionDualDerivedIso K D).symm (Iso.refl _)).trans
    ((homotopyDerivedEquiv _ C).symm.trans
    ((homotopyDualHomEquiv _ C).trans
    ((CategoryTheory.Linear.homCongr (Laurent K D) (Iso.refl _)
      ((homotopyQuotient (Laurent K D)).mapIso
        (complexDoubleDualIso (coefficientResolution K D))).symm).trans
    ((homotopyDerivedEquiv _ (coefficientResolution K D)).trans
    ((CategoryTheory.Linear.homCongr (Laurent K D) (Iso.refl _)
      (Toric.derivedIso K D 0)).trans
    (homotopyDerivedEquiv _ _).symm)))))

end
end Decoupling.HighDim.Torus
