import Decoupling.HighDim.ScalingLatticeProfile

/-! # Dual resolutions and profiles under a genuine coefficient-ring isomorphism -/

namespace Decoupling.HighDim.ScalingLattice.RingChange

open CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {A B : Type} [CommRing A] [CommRing B] (e : A ≃+* B)

abbrev rename : ModuleCat A ⥤ ModuleCat B := ModuleCat.restrictScalars e.symm.toRingHom

def homEquiv (M : ModuleCat A) :
    (rename e).obj (ModuleCat.of A (M ⟶ ModuleCat.of A A)) ≃ₗ[B]
      ((rename e).obj M ⟶ ModuleCat.of B B) where
  toFun f := ModuleCat.ofHom (X := (rename e).obj M) (Y := ModuleCat.of B B) {
    toFun x := e ((show M ⟶ ModuleCat.of A A from f) (show M from x))
    map_add' x y := by simp
    map_smul' b x := by
      change e ((show M ⟶ ModuleCat.of A A from f) (e.symm b • (show M from x))) =
        b * e ((show M ⟶ ModuleCat.of A A from f) (show M from x))
      rw [map_smul]
      simp }
  invFun g := ModuleCat.ofHom (X := M) (Y := ModuleCat.of A A) {
    toFun x := e.symm (g (show (rename e).obj M from x))
    map_add' x y := by simp
    map_smul' a x := by
      have h := g.hom.map_smul (e a) (show (rename e).obj M from x)
      change g (e.symm (e a) • x) = e a * g x at h
      change e.symm (g (a • x)) = a * e.symm (g x)
      simpa only [RingEquiv.symm_apply_apply, map_mul] using congrArg e.symm h }
  left_inv f := by
    apply ModuleCat.hom_ext
    ext x
    exact e.symm_apply_apply _
  right_inv g := by
    apply ModuleCat.hom_ext
    ext x
    exact e.apply_symm_apply _
  map_add' f g := by
    apply ModuleCat.hom_ext
    ext x
    exact e.map_add _ _
  map_smul' b f := by
    apply ModuleCat.hom_ext
    ext x
    change e (e.symm b * (show M ⟶ ModuleCat.of A A from f) x) =
      b * e ((show M ⟶ ModuleCat.of A A from f) x)
    simp

def resolution {M : ModuleCat A} (P : ProjectiveResolution M) :
    ProjectiveResolution ((rename e).obj M) := (rename e).mapProjectiveResolution P

def dualComplexIso {M : ModuleCat A} (P : ProjectiveResolution M) :
    ((rename e).mapHomologicalComplex (.up ℕ)).obj
      (ResolutionCohomology.dualComplex P (ModuleCat.of A A)) ≅
    ResolutionCohomology.dualComplex (resolution e P) (ModuleCat.of B B) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (homEquiv e (P.complex.X n)).toModuleIso)
    (by
      intro i j _
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      rfl)

def rHomComplexIso {M : ModuleCat A} (P : ProjectiveResolution M) :
    ((rename e).mapHomologicalComplex (.up ℤ)).obj
      (Profile.rHomComplex P (ModuleCat.of A A)) ≅
    Profile.rHomComplex (resolution e P) (ModuleCat.of B B) :=
  ExtendFunctor.iso (rename e) _ ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat B)).mapIso (dualComplexIso e P)

/-- Native positive RHom profiles commute with renaming an isomorphic ring. -/
def profileIso {M : ModuleCat A} (P : ProjectiveResolution M) :
    (rename e).mapDerivedCategory.obj (Profile.ofResolution P (ModuleCat.of A A)) ≅
      Profile.ofResolution (resolution e P) (ModuleCat.of B B) :=
  (rename e).mapDerivedCategoryFactors.app _ ≪≫
    ExactTruncation.derivedIso (rename e) _ 1 ≪≫
      DerivedCategory.Q.mapIso
        (((ComplexShape.embeddingUpIntGE 1).truncGEFunctor (ModuleCat B)).mapIso
          (rHomComplexIso e P))

end
end Decoupling.HighDim.ScalingLattice.RingChange
