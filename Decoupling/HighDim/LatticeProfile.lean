import Decoupling.HighDim.LatticeExt
import Decoupling.HighDim.ResolutionComparison
import Decoupling.HighDim.ExactTruncation
import Decoupling.HighDim.ExtendFunctor
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Decoupling.HighDim.LatticeCompatibility

/-!
# Restricting full dual projective-resolution complexes

The comparison is a degreewise trace isomorphism of the actual Hom
complexes for an arbitrary finite-index subgroup of the full lattice.
No rectangular-lattice assumption occurs. The derived truncation and
physical-check interfaces are connected in later declarations.
-/

namespace Decoupling.HighDim.LatticeProfile

open CategoryTheory CategoryTheory.Abelian LatticeRestriction LatticeExt
open scoped ModuleCat.Algebra
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] HasDerivedCategory.standard

variable (K : Type) [CommRing K] {D : ℕ}
  (Λ : AddSubgroup (Translation D)) [Λ.FiniteIndex]

instance restriction_preservesProjectiveObjects : (restriction K Λ).PreservesProjectiveObjects :=
  Functor.preservesProjectiveObjects_of_adjunction_of_preservesEpimorphisms
    (ModuleCat.restrictCoextendScalarsAdj (algebraMap (S K Λ) (Laurent K D)))

def restrictedResolution {M : ModuleCat (Laurent K D)} (P : ProjectiveResolution M) :
    ProjectiveResolution ((restriction K Λ).obj M) :=
  (restriction K Λ).mapProjectiveResolution P

/-- Forget only the bundled change-of-scalars wrapper on a Hom module. -/
def unbundleHom (M : ModuleCat (Laurent K D)) :
    (restriction K Λ).obj
      (ModuleCat.of (Laurent K D) (M ⟶ ModuleCat.of (Laurent K D) (Laurent K D))) ≃ₗ[S K Λ]
    (M →ₗ[Laurent K D] Laurent K D) where
  toFun f := (show M ⟶ ModuleCat.of (Laurent K D) (Laurent K D) from f).hom
  invFun f := ModuleCat.ofHom f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Bundle an S-linear functional on the same restricted underlying module. -/
def bundleRestrictedHom (M : ModuleCat (Laurent K D)) :
    (M →ₗ[S K Λ] S K Λ) ≃ₗ[S K Λ]
    ((restriction K Λ).obj M ⟶ ModuleCat.of (S K Λ) (S K Λ)) where
  toFun f := ModuleCat.ofHom {
    toFun x := f (show M from x)
    map_add' := f.map_add
    map_smul' := f.map_smul }
  invFun f := {
    toFun x := f (show (restriction K Λ).obj M from x)
    map_add' x y := f.hom.map_add x y
    map_smul' a x := f.hom.map_smul a x }
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The original-R dual, restricted to S, is the dual over S by the trace. -/
def homTraceEquiv (M : ModuleCat (Laurent K D)) :
    (restriction K Λ).obj
      (ModuleCat.of (Laurent K D) (M ⟶ ModuleCat.of (Laurent K D) (Laurent K D))) ≃ₗ[S K Λ]
    ((restriction K Λ).obj M ⟶ ModuleCat.of (S K Λ) (S K Λ)) :=
  ((unbundleHom K Λ M).trans (dualRestrictEquiv K Λ)).trans (bundleRestrictedHom K Λ M)

@[simp]
theorem homTraceEquiv_apply (M : ModuleCat (Laurent K D))
    (f : (restriction K Λ).obj
      (ModuleCat.of (Laurent K D) (M ⟶ ModuleCat.of (Laurent K D) (Laurent K D))))
    (x : (restriction K Λ).obj M) : homTraceEquiv K Λ M f x =
      τ K Λ ((show M ⟶ ModuleCat.of (Laurent K D) (Laurent K D) from f)
        (show M from x)) := rfl

def dualComplexIso {M : ModuleCat (Laurent K D)} (P : ProjectiveResolution M) :
    ((restriction K Λ).mapHomologicalComplex (.up ℕ)).obj
      (ResolutionCohomology.dualComplex P (ModuleCat.of (Laurent K D) (Laurent K D))) ≅
    ResolutionCohomology.dualComplex (restrictedResolution K Λ P)
      (ModuleCat.of (S K Λ) (S K Λ)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (homTraceEquiv K Λ (P.complex.X n)).toModuleIso)
    (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

def rHomComplexIso {M : ModuleCat (Laurent K D)} (P : ProjectiveResolution M) :
    ((restriction K Λ).mapHomologicalComplex (.up ℤ)).obj
      (Profile.rHomComplex P (ModuleCat.of (Laurent K D) (Laurent K D))) ≅
    Profile.rHomComplex (restrictedResolution K Λ P) (ModuleCat.of (S K Λ) (S K Λ)) :=
  ExtendFunctor.iso (restriction K Λ) _ ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat (S K Λ))).mapIso
      (dualComplexIso K Λ P)

/-- The entire positive RHom object commutes with scalar restriction.
The constructed isomorphism preserves extension data, not only Ext layers. -/
def profileRestrictionIso {M : ModuleCat (Laurent K D)} (P : ProjectiveResolution M) :
    (restriction K Λ).mapDerivedCategory.obj
      (Profile.ofResolution P (ModuleCat.of (Laurent K D) (Laurent K D))) ≅
    Profile.ofResolution (restrictedResolution K Λ P) (ModuleCat.of (S K Λ) (S K Λ)) :=
  (restriction K Λ).mapDerivedCategoryFactors.app _ ≪≫
    ExactTruncation.derivedIso (restriction K Λ) _ 1 ≪≫
      DerivedCategory.Q.mapIso
        (((ComplexShape.embeddingUpIntGE 1).truncGEFunctor (ModuleCat (S K Λ))).mapIso
          (rHomComplexIso K Λ P))

/-- The profile of the actual expanded physical check matrix over the retained subring. -/
def physicalProfile {q s r : ℕ} (c : CSS.Checks K D q s r) :
    DerivedCategory (ModuleCat (S K Λ)) :=
  Profile.ofResolution
    (projectiveResolution (conjugateS K Λ (LatticeCompatibility.reduced K Λ c)))
    (ModuleCat.of (S K Λ) (S K Λ))

/-- Full derived-profile compatibility with physical coarse graining. -/
def physicalProfileIso {q s r : ℕ} (c : CSS.Checks K D q s r) :
    (restriction K Λ).mapDerivedCategory.obj (Profile.S_X c) ≅ physicalProfile K Λ c :=
  profileRestrictionIso K Λ (Profile.resolution c) ≪≫
    ResolutionComparison.profileIsoOfModuleIso (ModuleCat.of (S K Λ) (S K Λ))
      (restrictedResolution K Λ (Profile.resolution c))
      (LatticeCompatibility.reducedConjugateIso K Λ c) _

end
end Decoupling.HighDim.LatticeProfile
