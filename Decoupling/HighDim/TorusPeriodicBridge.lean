import Decoupling.HighDim.TorusTensorModel
import Decoupling.HighDim.TorusLatticeCoordinates
import Decoupling.HighDim.TorusTensorLocalDuality

/-!
# Actual finite-torus logical supports and the restricted native profile

This is the counting bridge required by Corollary 3 for an arbitrary
finite-index period lattice. The left side is the actual check
kernel/image quotient. The right side uses the actual native profile of
the physically restricted checks. No layer triviality, profile splitting,
or containment in the common translation kernel is assumed.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits Matrix FiniteResolution ScalingLattice
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

variable {K : Type} [Field K] {D q s r : ℕ}

/-- Actual checks with every translation in the current lattice set to
one. -/
def augmentationWindow (c : CSS.Checks K D q s r) (hc : c.Topological) :
    ShortComplex (ModuleCat K) :=
  ShortComplex.moduleCatMk ((dagger c.H_Z).map augmentation).mulVecLin
    (c.H_X.map augmentation).mulVecLin (by
      apply LinearMap.ext
      intro v
      funext i
      change ((c.H_X.map augmentation) *ᵥ ((dagger c.H_Z).map augmentation *ᵥ v)) i = 0
      rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, c.checks_commute hc]
      simp)

def augmentationExtensionWindowIso (c : CSS.Checks K D q s r) (hc : c.Topological) :
    (checkWindow c hc).map (ModuleCat.extendScalars augmentation) ≅ augmentationWindow c hc :=
  ShortComplex.isoMk (extensionFreeIso augmentation r)
    (extensionFreeIso augmentation q) (extensionFreeIso augmentation s)
    (extensionFreeIso_naturality _ (dagger c.H_Z)).symm
    (extensionFreeIso_naturality _ c.H_X).symm

def augmentationTensorWindowIso (c : CSS.Checks K D q s r) (hc : c.Topological) :
    (tensorAugmentation K D (cssComplex c hc)).sc' (-1) 0 1 ≅ augmentationWindow c hc := by
  change ((cssComplex c hc).sc' (-1) 0 1).map
    (ModuleCat.extendScalars (augmentation : Laurent K D →+* K)) ≅ augmentationWindow c hc
  exact (ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).mapShortComplex.mapIso
    (cssWindowIso c hc) ≪≫ augmentationExtensionWindowIso c hc

/-- Augmented actual checks count morphisms from the native torus probe. -/
def augmentationWindowProfileEquiv (c : CSS.Checks K D q s r) (hc : c.Topological) :
    (augmentationWindow c hc).homology ≃ₗ[K]
      homCoefficients (probe K D) (Profile.S_X c) :=
  (((ShortComplex.homologyFunctor (ModuleCat K)).mapIso
    (augmentationTensorWindowIso c hc)).symm.toLinearEquiv.trans
      (((tensorAugmentation K D (cssComplex c hc)).homologyIsoSc'
        (-1) 0 1 (by simp) (by simp)).symm.toLinearEquiv.trans
          ((tensorLocalDuality K D (cssComplex c hc) (-(D + 2 : ℕ))).trans
            (homCoefficientsIso (probe K D) (cssComplex_profileIso c hc)).toLinearEquiv)))

variable (L : AddSubgroup (Translation D)) [L.FiniteIndex] (e : L ≃+ Translation D)

/-- The finite-period physical window equals the augmented window after
actual restriction to exactly the same lattice. -/
def periodicAugmentationWindowIso (c : CSS.Checks K D q s r) (hc : c.Topological) :
    periodicSc L c hc ≅ augmentationWindow (physicalChecks K L e c)
      (physicalChecks_topological K L e c hc) :=
  ShortComplex.isoMk (periodicVectorCoordinates K L r).toModuleIso
    (periodicVectorCoordinates K L q).toModuleIso
    (periodicVectorCoordinates K L s).toModuleIso
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      change ((dagger (physicalChecks K L e c).H_Z).map augmentation) *ᵥ
        periodicVectorCoordinates K L r v =
          periodicVectorCoordinates K L q (((dagger c.H_Z).map (periodMap L)) *ᵥ v)
      change ((dagger (physicalMatrix K L e c.H_Z)).map augmentation) *ᵥ _ = _
      rw [← physicalMatrix_dagger]
      exact (periodicVectorCoordinates_naturality K L e (dagger c.H_Z) v).symm)
    (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      exact (periodicVectorCoordinates_naturality K L e c.H_X v).symm)

/-- Actual finite-torus logical support space equals the genuine native
representable functor on the profile of the physically restricted code. -/
def logicalProfileEquiv (c : CSS.Checks K D q s r) (hc : c.Topological) :
    Logical L c hc ≃ₗ[K]
      homCoefficients (probe K D) (Profile.S_X (physicalChecks K L e c)) :=
  (periodicHomologyEquiv L c hc).symm.trans
    (((ShortComplex.homologyFunctor (ModuleCat K)).mapIso
      (periodicAugmentationWindowIso L e c hc)).toLinearEquiv.trans
        (augmentationWindowProfileEquiv (physicalChecks K L e c)
          (physicalChecks_topological K L e c hc)))

theorem logicalQudits_eq_profile (c : CSS.Checks K D q s r) (hc : c.Topological) :
    logicalQudits L c hc = Module.finrank K
      (homCoefficients (probe K D) (Profile.S_X (physicalChecks K L e c))) :=
  (logicalProfileEquiv L e c hc).finrank_eq

end
end Decoupling.HighDim.Torus
