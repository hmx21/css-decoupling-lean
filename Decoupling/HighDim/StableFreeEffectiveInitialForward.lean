import Decoupling.HighDim.StableFreeEffectiveInitialMatrix

/-!
# HD012 the other direction of the initial split-retraction isomorphism

The first Schanuel lift uses the inverse split isomorphism. Absorbing the
eventual stable complement needs its forward map too. Both quotient
coordinates and actual complement coordinates are explicit here.
-/
namespace Decoupling.HighDim.StableFree.Effective.Initial.Data
open Matrix CategoryTheory
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R] {M N : ModuleCat.{u} R}
  {c n p e rel : ℕ} (a : Initial.Data M N c n p e rel)

def rhoLift : (Power R n × Power R p) →ₗ[R] Power R c :=
  a.G.comp (LinearMap.fst _ _ _) + a.Z.comp (LinearMap.snd _ _ _)

def forwardN : (Power R n × Power R p) →ₗ[R] Power R n :=
  LinearMap.fst _ _ _ - a.F.comp a.rhoLift

def forwardP : (Power R n × Power R p) →ₗ[R] Power R p :=
  LinearMap.snd _ _ _ - a.X.comp a.rhoLift

def forwardQ : (Power R n × Power R p) →ₗ[R] Power R (e+p) :=
  (powerAdd e p).toLinearMap.comp ((a.Y.comp a.forwardN).prod a.forwardP)

def forwardLift : Power R (n+p) →ₗ[R] Power R (c+(e+p)) :=
  (powerAdd c (e+p)).toLinearMap.comp
    ((a.rhoLift.prod a.forwardQ).comp (powerAdd n p).symm.toLinearMap)

def nativeKernel (z : Power R n × Power R p) : a.Complement :=
  StableCokernel.kernelProjection (StableCokernel.sectionMap a.f a.xiM)
    (StableCokernel.retraction a.g a.zetaM)
    (StableCokernel.retraction_section a.f a.g a.xiM a.zetaM a.errorM)
      (a.piN z.1,z.2)

theorem rhoLift_projects (z : Power R n × Power R p) :
    a.piM (a.rhoLift z) = a.g (a.piN z.1) + a.zetaM z.2 := by
  change a.piM (a.G z.1 + a.Z z.2) = _
  rw [a.piM.map_add, a.G_apply, a.Z_apply]

theorem forwardQ_embed (z : Power R n × Power R p) :
    a.forwardQ z = a.complement.embed (a.nativeKernel z) := by
  change powerAdd e p (a.Y (z.1 - a.F (a.rhoLift z)), z.2 - a.X (a.rhoLift z)) =
    powerAdd e p
      (a.xiN (a.piN z.1 - a.f (a.g (a.piN z.1) + a.zetaM z.2)),
       z.2 - a.xiM (a.g (a.piN z.1) + a.zetaM z.2))
  rw [a.Y_apply, a.piN.map_sub, a.F_apply, a.X_apply, a.rhoLift_projects]

/-- The displayed free-coordinate map lifts the actual forward split
isomorphism, including its genuine complement component. -/
theorem forwardLift_projects (x : Power R (n+p)) :
    (a.piM.prodMap LinearMap.id) (a.sourceRight.project (a.forwardLift x)) =
      StableCokernel.stableProjectiveEquiv a.f a.g a.xiM a.zetaM a.errorM
        (a.alpha (a.sourceLeft.project x)) := by
  let z := (powerAdd n p).symm x
  change (a.piM ((powerAdd c (e+p)).symm
      (powerAdd c (e+p) (a.rhoLift z,a.forwardQ z))).1,
    a.complement.project ((powerAdd c (e+p)).symm
      (powerAdd c (e+p) (a.rhoLift z,a.forwardQ z))).2) = _
  rw [LinearEquiv.symm_apply_apply, a.forwardQ_embed, FiniteRetract.project_embed,
    a.rhoLift_projects]
  rfl

def matrixRho := joinCols a.matrixG a.matrixZ
def matrixForwardN :=
  joinCols (1 : Matrix (Fin n) (Fin n) R) (0 : Matrix (Fin n) (Fin p) R) -
    a.matrixF * a.matrixRho
def matrixForwardP :=
  joinCols (0 : Matrix (Fin p) (Fin n) R) (1 : Matrix (Fin p) (Fin p) R) -
    a.matrixX * a.matrixRho
def matrixForwardQ := joinRows (a.matrixY * a.matrixForwardN) a.matrixForwardP
def matrixForward := joinRows a.matrixRho a.matrixForwardQ

theorem matrixRho_apply (x : Power R (n+p)) :
    a.matrixRho *ᵥ x = a.rhoLift ((powerAdd n p).symm x) := by
  rw [matrixRho, joinCols_mulVec]
  simp only [matrixG, matrixZ, LinearMap.toMatrix'_mulVec]
  rfl

theorem matrixForwardN_apply (x : Power R (n+p)) :
    a.matrixForwardN *ᵥ x = a.forwardN ((powerAdd n p).symm x) := by
  rw [matrixForwardN, Matrix.sub_mulVec, joinCols_mulVec, Matrix.one_mulVec,
    Matrix.zero_mulVec, add_zero, ← Matrix.mulVec_mulVec, matrixRho_apply]
  simp only [matrixF, LinearMap.toMatrix'_mulVec]
  rfl

theorem matrixForwardP_apply (x : Power R (n+p)) :
    a.matrixForwardP *ᵥ x = a.forwardP ((powerAdd n p).symm x) := by
  rw [matrixForwardP, Matrix.sub_mulVec, joinCols_mulVec, Matrix.one_mulVec,
    Matrix.zero_mulVec, zero_add, ← Matrix.mulVec_mulVec, matrixRho_apply]
  simp only [matrixX, LinearMap.toMatrix'_mulVec]
  rfl

theorem matrixForwardQ_apply (x : Power R (n+p)) :
    a.matrixForwardQ *ᵥ x = a.forwardQ ((powerAdd n p).symm x) := by
  rw [matrixForwardQ, joinRows_mulVec, ← Matrix.mulVec_mulVec,
    matrixForwardN_apply, matrixForwardP_apply]
  simp only [matrixY, LinearMap.toMatrix'_mulVec]
  rfl

theorem matrixForward_apply (x : Power R (n+p)) :
    a.matrixForward *ᵥ x = a.forwardLift x := by
  rw [matrixForward, joinRows_mulVec, matrixRho_apply, matrixForwardQ_apply]
  rfl

end
end Decoupling.HighDim.StableFree.Effective.Initial.Data
