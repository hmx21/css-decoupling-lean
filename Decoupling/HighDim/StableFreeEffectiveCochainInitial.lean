import Decoupling.HighDim.StableFreeEffectiveInitialForwardProgram
import Decoupling.HighDim.StableFreeEffectiveInitialHomotopy
import Decoupling.HighDim.StableFreeEffectiveCheckProgram

/-!
# Connecting the actual initial homotopy formulas to the effective recursion

No caller supplies a comparison lift, projective basis, scalar solution or
stable complement. The seven stored coordinate matrices are the original
homotopy data, and the frozen Initial program constructs the genuine arrows.
-/
namespace Decoupling.HighDim.StableFree.Effective.CochainProgram
open Matrix LaurentArithmetic ArithmeticCost
universe u
variable {K : Type u} [Field K] {D c n p e rel h h₀ length : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Pure field-preserving view of the actual six initial output matrices. -/
def initialStage (o : Initial.Output K D c n p e rel h) :
    PresentedStageArrays K D (n+p) (n+p) (c+(e+p)) rel h where
  left := o.alpha
  right := o.beta
  relations := o.relations
  sourceLeft := o.leftProjector
  sourceRight := o.rightProjector

noncomputable section
variable {M N : ModuleCat.{u} (Laurent K D)}

def freeAt (k : ℕ) : RetractAt (ModuleCat.of (Laurent K D) (Power (Laurent K D) k)) k :=
  ⟨LinearMap.id,LinearMap.id,by ext x; rfl⟩

def complementAt (a : Initial.Data M N c n p e rel) : RetractAt a.Complement (e+p) :=
  ⟨a.complement.embed,a.complement.project,a.complement.retract⟩

def initialEquiv (a : Initial.Data M N c n p e rel) :
    (N × Power (Laurent K D) p) ≃ₗ[Laurent K D] (M × a.Complement) :=
  StableCokernel.stableProjectiveEquiv a.f a.g a.xiM a.zetaM a.errorM

theorem initialStage_solvable (i : Initial.Inputs K D c n p e rel h)
    (a : Initial.Data M N c n p e rel) (hi : Initial.Realizes i a) :
    (initialStage i.runComplete.value.initial).Solvable := by
  have ho := Initial.run_correct i a hi
  unfold PresentedStageArrays.Solvable
  change (∃ z, liftCoefficients (matrixDenote i.run.value.alpha) (matrixDenote i.run.value.relations)
      (matrixDenote i.run.value.leftProjector) (matrixDenote i.run.value.rightProjector) *ᵥ z =
        liftStack (matrixDenote i.run.value.beta) 0 0) ∧
    (∃ z, liftCoefficients (matrixDenote i.run.value.beta) (matrixDenote i.run.value.relations)
      (matrixDenote i.run.value.rightProjector) (matrixDenote i.run.value.leftProjector) *ᵥ z =
        liftStack (matrixDenote i.run.value.alpha) 0 0)
  rw [ho.1,ho.2.1,ho.2.2.1,ho.2.2.2.1,ho.2.2.2.2.1]
  exact ⟨PresentedTarget.lift_system_solvable _ _ _ _ _ a.alphaArrow a.betaArrow a.alpha_surjective,
    PresentedTarget.lift_system_solvable _ _ _ _ _ a.betaArrow a.alphaArrow a.beta_surjective⟩

variable [DecidableEq K]

theorem initialStage_valid_of_output (a : Initial.Data M N c n p e rel)
    (o : Initial.Output K D c n p e rel h)
    (ho : matrixDenote o.alpha = a.alphaArrow.matrix ∧ matrixDenote o.beta = a.betaArrow.matrix ∧
      matrixDenote o.relations = a.target.relationMatrix ∧
      matrixDenote o.leftProjector = a.sourceLeft.projector ∧
      matrixDenote o.rightProjector = a.sourceRight.projector ∧
      matrixDenote o.complementProjector = a.complement.projector)
    (F : DenseTower K D h₀ length n) (G : DenseTower K D h₀ length c)
    (hF : F.Models (ModuleCat.of (Laurent K D) (LinearMap.ker a.piN)) (LinearMap.ker a.piN).subtype)
    (hG : G.Models (ModuleCat.of (Laurent K D) (LinearMap.ker a.piM)) (LinearMap.ker a.piM).subtype)
    (hs : (initialStage o).Solvable) :
    StateValid F G (firstUpdate (identityDense K D h p) o.complementProjector
      (solvePresentedStage (initialStage o) hs).value.1
      (solvePresentedStage (initialStage o) hs).value.2.1).value := by
  have hp : (freeAt (K := K) (D := D) p).model.projector = 1 := by
    apply Matrix.mulVec_injective
    funext x
    rw [FiniteRetract.projector_mulVec,Matrix.one_mulVec]
    rfl
  exact firstStage_valid (M := N) (N := M)
    (P := ModuleCat.of (Laurent K D) (Power (Laurent K D) p)) (Q := a.Complement)
    (F₀ := ModuleCat.of (Laurent K D) (Power (Laurent K D) n))
    (G₀ := ModuleCat.of (Laurent K D) (Power (Laurent K D) c)) a.piN a.piM (initialEquiv a) (LinearEquiv.refl _ _) (LinearEquiv.refl _ _)
    (freeAt p) (complementAt a) a.target a.alphaArrow a.betaArrow
    (initialStage o) ho.1 ho.2.1 ho.2.2.1 ho.2.2.2.1 ho.2.2.2.2.1
    F G hF hG _ _ (identityDense_correct.trans hp.symm) ho.2.2.2.2.2 hs

theorem initialStage_valid (i : Initial.Inputs K D c n p e rel h)
    (a : Initial.Data M N c n p e rel) (hi : Initial.Realizes i a)
    (F : DenseTower K D h₀ length n) (G : DenseTower K D h₀ length c)
    (hF : F.Models (ModuleCat.of (Laurent K D) (LinearMap.ker a.piN)) (LinearMap.ker a.piN).subtype)
    (hG : G.Models (ModuleCat.of (Laurent K D) (LinearMap.ker a.piM)) (LinearMap.ker a.piM).subtype) :
    StateValid F G (firstUpdate (identityDense K D (Initial.radius5 h) p)
      i.runComplete.value.initial.complementProjector
      (solvePresentedStage (initialStage i.runComplete.value.initial) (initialStage_solvable i a hi)).value.1
      (solvePresentedStage (initialStage i.runComplete.value.initial) (initialStage_solvable i a hi)).value.2.1).value :=
  initialStage_valid_of_output a i.runComplete.value.initial (Initial.run_correct i a hi)
    F G hF hG (initialStage_solvable i a hi)

end
end Decoupling.HighDim.StableFree.Effective.CochainProgram
