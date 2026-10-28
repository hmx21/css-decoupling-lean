import Decoupling.HighDim.TorusTensorDual

/-!
# Tensor homology and native derived local duality over the coefficient field

For every bounded-below finite free Laurent cochain complex, the actual
augmentation tensor homology is coefficient-linearly equivalent to the
native morphism space `F[-D] ⟶ C`. The equivalence is assembled from actual
tensor evaluation, genuine cycles/boundaries, ordinary cochain duality,
and the signed Koszul resolution.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (D : ℕ)

/-- Augmentation followed by coefficient restriction recovers the
original coefficient module, with its actual scalar action. -/
def augmentationCoefficientsIso :
    ModuleCat.restrictScalars (augmentation : Laurent K D →+* K) ⋙
      ModuleCat.restrictScalars (constant : K →+* Laurent K D) ≅ 𝟭 (ModuleCat K) :=
  (ModuleCat.restrictScalarsComp (constant : K →+* Laurent K D) augmentation).symm ≪≫
    ModuleCat.restrictScalarsId' _ (by ext a; exact augmentation_constant a)

def augmentationCoefficientsWindowIso (S : ShortComplex (ModuleCat K)) :
    (S.map (ModuleCat.restrictScalars (augmentation : Laurent K D →+* K))).map
      (ModuleCat.restrictScalars (constant : K →+* Laurent K D)) ≅ S :=
  ShortComplex.isoMk ((augmentationCoefficientsIso K D).app S.X₁)
    ((augmentationCoefficientsIso K D).app S.X₂)
    ((augmentationCoefficientsIso K D).app S.X₃)
    ((augmentationCoefficientsIso K D).hom.naturality S.f).symm
    ((augmentationCoefficientsIso K D).hom.naturality S.g).symm

abbrev tensorAugmentation (C : CochainComplex (ModuleCat (Laurent K D)) ℤ) :=
  ((ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).mapHomologicalComplex
    (.up ℤ)).obj C

/-- Ring-linear window form of finite-perfect local duality. -/
def tensorWindowLocalDuality (C : CochainComplex (ModuleCat (Laurent K D)) ℤ)
    [∀ n, Module.Finite (Laurent K D) (C.X n)]
    [∀ n, Module.Free (Laurent K D) (C.X n)] (b : ℤ) [C.IsStrictlyGE b] :
    ((C.sc' (-1) 0 1).map (extensionRestricted (augmentation : Laurent K D →+* K))).homology
      ≃ₗ[Laurent K D] (probe K D ⟶ DerivedCategory.Q.obj C) :=
  ((ShortComplex.homologyFunctor (ModuleCat (Laurent K D))).mapIso
    (tensorDualWindowIso augmentation C)).toLinearEquiv.trans
      ((homSingleHomologyEquiv (complexDual (Laurent K D) C)
        (Koszul.coefficientModule K D)).trans (localDualityHomEquiv K D C b).symm)

/-- Coefficient-linear form of the same equivalence. -/
def tensorWindowLocalDualityCoefficients (C : CochainComplex (ModuleCat (Laurent K D)) ℤ)
    [∀ n, Module.Finite (Laurent K D) (C.X n)]
    [∀ n, Module.Free (Laurent K D) (C.X n)] (b : ℤ) [C.IsStrictlyGE b] :
    Layers.coefficients
      (((C.sc' (-1) 0 1).map (extensionRestricted
        (augmentation : Laurent K D →+* K))).homology) ≃ₗ[K]
      homCoefficients (probe K D) (DerivedCategory.Q.obj C) := by
  let e := tensorWindowLocalDuality K D C b
  exact {
    toFun := e
    invFun := e.symm
    left_inv := e.symm_apply_apply
    right_inv := e.apply_symm_apply
    map_add' := e.map_add
    map_smul' a x := e.map_smul (constant (D := D) a) x }

/-- Actual augmentation tensor homology is the actual native derived
representable functor, with its coefficient-field linear structure. -/
def tensorLocalDuality (C : CochainComplex (ModuleCat (Laurent K D)) ℤ)
    [∀ n, Module.Finite (Laurent K D) (C.X n)]
    [∀ n, Module.Free (Laurent K D) (C.X n)] (b : ℤ) [C.IsStrictlyGE b] :
    (tensorAugmentation K D C).homology 0 ≃ₗ[K]
      homCoefficients (probe K D) (DerivedCategory.Q.obj C) :=
  ((tensorAugmentation K D C).homologyIsoSc' (-1) 0 1 (by simp) (by simp)).toLinearEquiv.trans
    (((ShortComplex.homologyFunctor (ModuleCat K)).mapIso
      (augmentationCoefficientsWindowIso K D
        ((tensorAugmentation K D C).sc' (-1) 0 1)).symm).toLinearEquiv.trans
      ((((C.sc' (-1) 0 1).map (extensionRestricted
        (augmentation : Laurent K D →+* K))).mapHomologyIso
          (ModuleCat.restrictScalars (constant : K →+* Laurent K D))).toLinearEquiv.trans
            (tensorWindowLocalDualityCoefficients K D C b)))

end
end Decoupling.HighDim.Torus
