import Decoupling.HighDim.StableFreeEffectivePresentations

/-!
# HD012 explicit first Schanuel lifting square from the actual homotopy errors

This auxiliary interface retains the actual quotient maps, actual error
factorizations and the known free-coordinate lifts from a homotopy
equivalence. It constructs the first two presented arrows by displayed
formulas; it never chooses a lift or a basis of the complement.
The full algorithm must supply these intermediate identities from its
computed comparison and contraction.
-/
namespace Decoupling.HighDim.StableFree.Effective.Initial
open CategoryTheory Matrix
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R]
  {M N : ModuleCat.{u} R} {c n p e rel : ℕ}

structure Data (M N : ModuleCat.{u} R) (c n p e rel : ℕ) where
  piM : Power R c →ₗ[R] M
  piN : Power R n →ₗ[R] N
  surjM : Function.Surjective piM
  surjN : Function.Surjective piN
  relations : Matrix (Fin n) (Fin rel) R
  kerN : piN.ker = relations.mulVecLin.range
  f : M →ₗ[R] N
  g : N →ₗ[R] M
  xiM : M →ₗ[R] Power R p
  zetaM : Power R p →ₗ[R] M
  xiN : N →ₗ[R] Power R e
  zetaN : Power R e →ₗ[R] N
  errorM : LinearMap.id - g.comp f = zetaM.comp xiM
  errorN : LinearMap.id - f.comp g = zetaN.comp xiN
  F : Power R c →ₗ[R] Power R n
  G : Power R n →ₗ[R] Power R c
  X : Power R c →ₗ[R] Power R p
  Y : Power R n →ₗ[R] Power R e
  Z : Power R p →ₗ[R] Power R c
  T : Power R e →ₗ[R] Power R n
  F_lifts : piN.comp F = f.comp piM
  G_lifts : piM.comp G = g.comp piN
  X_lifts : X = xiM.comp piM
  Y_lifts : Y = xiN.comp piN
  Z_lifts : piM.comp Z = zetaM
  T_lifts : piN.comp T = zetaN

namespace Data
variable (a : Data M N c n p e rel)

abbrev Complement := ModuleCat.of R (StableCokernel.Complement a.g a.zetaM)

def free (k : ℕ) : FiniteRetract (ModuleCat.of R (Power R k)) :=
  FiniteRetract.ofCoordinates k (LinearEquiv.refl _ _)

def complement : FiniteRetract a.Complement :=
  complementRetract (M := M) (N := N)
    (P := ModuleCat.of R (Power R p)) (Q := ModuleCat.of R (Power R e))
    a.f a.g a.xiM a.zetaM a.xiN a.zetaN a.errorM a.errorN
    (free p) (free e)

def quotientPresentation : PresentedTarget N where
  ambient := N
  size := n
  relationCount := rel
  relationMatrix := a.relations
  project := a.piN
  surjective := a.surjN
  ker_project := a.kerN
  embed := LinearMap.id
  embed_injective := Function.injective_id

def target : PresentedTarget (ModuleCat.of R (N × Power R p)) :=
  a.quotientPresentation.prod (free p)

def sourceLeft (_ : Data M N c n p e rel) :
    FiniteRetract (ModuleCat.of R (Power R n × Power R p)) :=
  (free n).prod (free p)

def sourceRight : FiniteRetract (ModuleCat.of R (Power R c × a.Complement)) :=
  (free c).prod a.complement

def alpha : (Power R n × Power R p) →ₗ[R] (N × Power R p) :=
  a.piN.prodMap LinearMap.id

def beta : (Power R c × a.Complement) →ₗ[R] (N × Power R p) :=
  (StableCokernel.stableProjectiveEquiv a.f a.g a.xiM a.zetaM a.errorM).symm.toLinearMap.comp
    (a.piM.prodMap LinearMap.id)

def leftLift : (Power R e × Power R p) →ₗ[R] Power R n :=
  a.T.comp (LinearMap.fst _ _ _) - a.F.comp (a.Z.comp (LinearMap.snd _ _ _))

def rightLift : (Power R e × Power R p) →ₗ[R] Power R c :=
  a.G.comp a.leftLift + a.Z.comp (LinearMap.snd _ _ _)

def complementN : (Power R e × Power R p) →ₗ[R] Power R n :=
  a.leftLift - a.F.comp a.rightLift

def complementP : (Power R e × Power R p) →ₗ[R] Power R p :=
  LinearMap.snd _ _ _ - a.X.comp a.rightLift

theorem F_apply (x : Power R c) : a.piN (a.F x) = a.f (a.piM x) :=
  DFunLike.congr_fun a.F_lifts x
theorem G_apply (x : Power R n) : a.piM (a.G x) = a.g (a.piN x) :=
  DFunLike.congr_fun a.G_lifts x
theorem X_apply (x : Power R c) : a.X x = a.xiM (a.piM x) :=
  DFunLike.congr_fun a.X_lifts x
theorem Y_apply (x : Power R n) : a.Y x = a.xiN (a.piN x) :=
  DFunLike.congr_fun a.Y_lifts x
theorem Z_apply (x : Power R p) : a.piM (a.Z x) = a.zetaM x :=
  DFunLike.congr_fun a.Z_lifts x
theorem T_apply (x : Power R e) : a.piN (a.T x) = a.zetaN x :=
  DFunLike.congr_fun a.T_lifts x

theorem leftLift_projects (x : Power R e × Power R p) :
    a.piN (a.leftLift x) = a.zetaN x.1 - a.f (a.zetaM x.2) := by
  change a.piN (a.T x.1 - a.F (a.Z x.2)) = _
  rw [a.piN.map_sub, a.T_apply, a.F_apply, a.Z_apply]

theorem rightLift_projects (x : Power R e × Power R p) :
    a.piM (a.rightLift x) =
      a.g (a.zetaN x.1 - a.f (a.zetaM x.2)) + a.zetaM x.2 := by
  change a.piM (a.G (a.leftLift x) + a.Z x.2) = _
  rw [a.piM.map_add, a.G_apply, a.Z_apply, a.leftLift_projects]

theorem complementRetraction_projects (x : Power R e × Power R p) :
    ((StableCokernel.complementRetraction a.f a.g a.xiM a.zetaM a.zetaN a.errorM x :
      a.Complement) : N × Power R p) =
      (a.piN (a.complementN x), a.complementP x) := by
  apply Prod.ext
  · change (a.zetaN x.1 - a.f (a.zetaM x.2)) -
      a.f (a.g (a.zetaN x.1 - a.f (a.zetaM x.2)) + a.zetaM x.2) =
        a.piN (a.leftLift x - a.F (a.rightLift x))
    rw [a.piN.map_sub, a.F_apply, a.leftLift_projects, a.rightLift_projects]
  · change x.2 - a.xiM (a.g (a.zetaN x.1 - a.f (a.zetaM x.2)) + a.zetaM x.2) =
        x.2 - a.X (a.rightLift x)
    rw [a.X_apply, a.rightLift_projects]

def betaLift : Power R (c + (e + p)) →ₗ[R] Power R (n + p) :=
  (powerAdd n p).toLinearMap.comp
    (((a.F.comp (LinearMap.fst _ _ _)).prod (a.X.comp (LinearMap.fst _ _ _)) +
      (a.complementN.prod a.complementP).comp
        ((powerAdd e p).symm.toLinearMap.comp (LinearMap.snd _ _ _))).comp
      (powerAdd c (e+p)).symm.toLinearMap)

def alphaArrow : PresentedTarget.Arrow a.sourceLeft a.target a.alpha :=
  PresentedTarget.Arrow.ofFreeLift _ _ _ LinearMap.id (by
    apply LinearMap.ext
    intro x
    rfl)

theorem target_project (v : Power R n × Power R p) :
    a.target.project (powerAdd n p v) = (a.piN v.1, v.2) := by
  change (a.piN ((powerAdd n p).symm (powerAdd n p v)).1,
    ((powerAdd n p).symm (powerAdd n p v)).2) = _
  rw [LinearEquiv.symm_apply_apply]

theorem sourceRight_project (x : Power R (c + (e+p))) :
    a.sourceRight.project x =
      (((powerAdd c (e+p)).symm x).1,
        StableCokernel.complementRetraction a.f a.g a.xiM a.zetaM a.zetaN a.errorM
          ((powerAdd e p).symm ((powerAdd c (e+p)).symm x).2)) := rfl

theorem beta_apply (x : Power R c × a.Complement) :
    a.beta x = (a.f (a.piM x.1) + x.2.val.1, a.xiM (a.piM x.1) + x.2.val.2) := rfl

theorem betaLift_projects :
    a.target.project.comp a.betaLift =
      a.target.embed.comp (a.beta.comp a.sourceRight.project) := by
  apply LinearMap.ext
  intro x
  let z := (powerAdd c (e+p)).symm x
  let y := (powerAdd e p).symm z.2
  change a.target.project (a.betaLift x) = a.target.embed (a.beta (a.sourceRight.project x))
  rw [a.sourceRight_project, a.beta_apply]
  change a.target.project (powerAdd n p (a.F z.1 + a.complementN y, a.X z.1 + a.complementP y)) =
    (a.f (a.piM z.1) +
      (StableCokernel.complementRetraction a.f a.g a.xiM a.zetaM a.zetaN a.errorM y).val.1,
     a.xiM (a.piM z.1) +
      (StableCokernel.complementRetraction a.f a.g a.xiM a.zetaM a.zetaN a.errorM y).val.2)
  rw [a.target_project]
  rw [a.complementRetraction_projects y]
  apply Prod.ext
  · rw [a.piN.map_add, a.F_apply]
  · exact congrArg (fun v => v + a.complementP y) (a.X_apply z.1)

/-- The initial opposite arrow is built by the displayed formulas,
without invoking projectivity to choose a representative matrix. -/
def betaArrow : PresentedTarget.Arrow a.sourceRight a.target a.beta :=
  PresentedTarget.Arrow.ofFreeLift _ _ _ a.betaLift a.betaLift_projects

theorem alpha_surjective : Function.Surjective a.alpha := by
  rintro ⟨x,y⟩
  obtain ⟨v,hv⟩ := a.surjN x
  exact ⟨(v,y), Prod.ext hv rfl⟩

theorem beta_surjective : Function.Surjective a.beta := by
  intro x
  let z := StableCokernel.stableProjectiveEquiv a.f a.g a.xiM a.zetaM a.errorM x
  obtain ⟨v,hv⟩ := a.surjM z.1
  refine ⟨(v,z.2), ?_⟩
  change (StableCokernel.stableProjectiveEquiv a.f a.g a.xiM a.zetaM a.errorM).symm
    (a.piM v,z.2) = x
  rw [hv]
  exact LinearEquiv.symm_apply_apply _ x

end Data
end
end Decoupling.HighDim.StableFree.Effective.Initial
