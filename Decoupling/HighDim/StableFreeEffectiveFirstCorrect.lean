import Decoupling.HighDim.StableFreeEffectiveFirstStage

/-! The genuine initial quotient arrows initialize the recursive dense state. -/
namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic
universe u
variable {K : Type u} [Field K] {D h h₀ length a b p q : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {M N P Q F₀ G₀ : ModuleCat.{u} (Laurent K D)}
  (f : F₀ →ₗ[Laurent K D] M) (g : G₀ →ₗ[Laurent K D] N)
  (e : (M × P) ≃ₗ[Laurent K D] (N × Q))
  (cF : F₀ ≃ₗ[Laurent K D] Power (Laurent K D) a)
  (cG : G₀ ≃ₗ[Laurent K D] Power (Laurent K D) b)
  (rp : RetractAt P p) (rq : RetractAt Q q)
  (target : PresentedTarget (ModuleCat.of (Laurent K D) (M × P)))
  (α : PresentedTarget.Arrow ((FiniteRetract.ofCoordinates a cF).prod rp.model) target (stageLeft f))
  (β : PresentedTarget.Arrow ((FiniteRetract.ofCoordinates b cG).prod rq.model) target (stageRight g e))
  (data : PresentedStageArrays K D target.size (a+p) (b+q) target.relationCount h)
  (hα : matrixDenote data.left = α.matrix) (hβ : matrixDenote data.right = β.matrix)
  (hD : matrixDenote data.relations = target.relationMatrix)
  (hS : matrixDenote data.sourceLeft = ((FiniteRetract.ofCoordinates a cF).prod rp.model).projector)
  (hT : matrixDenote data.sourceRight = ((FiniteRetract.ofCoordinates b cG).prod rq.model).projector)

include hα hβ hD hS hT

/-- Both initial lift systems follow from the actual surjective covers. -/
theorem firstStage_solvable (hf : Function.Surjective f) (hg : Function.Surjective g) :
    data.Solvable := by
  unfold PresentedStageArrays.Solvable
  rw [hα,hβ,hD,hS,hT]
  exact ⟨PresentedTarget.lift_system_solvable _ _ _ _ _ α β (stageLeft_surjective f hf),
    PresentedTarget.lift_system_solvable _ _ _ _ _ β α (stageRight_surjective g hg e)⟩

variable [DecidableEq K]

/-- The first actual solved Schanuel state has the supplied genuine tail
resolutions. No initial representation or free-complement basis is selected. -/
theorem firstStage_valid
    (F : DenseTower K D h₀ length a) (G : DenseTower K D h₀ length b)
    (hF : F.Models (ModuleCat.of (Laurent K D) (LinearMap.ker f))
      (cF.toLinearMap.comp (LinearMap.ker f).subtype))
    (hG : G.Models (ModuleCat.of (Laurent K D) (LinearMap.ker g))
      (cG.toLinearMap.comp (LinearMap.ker g).subtype))
    (EP : DenseMatrix K D p p h) (EQ : DenseMatrix K D q q h)
    (hEP : matrixDenote EP = rp.model.projector) (hEQ : matrixDenote EQ = rq.model.projector)
    (hs : data.Solvable) :
    StateValid F G (firstUpdate EP EQ (solvePresentedStage data hs).value.1
      (solvePresentedStage data hs).value.2.1).value := by
  let S := (FiniteRetract.ofCoordinates a cF).prod rp.model
  let T := (FiniteRetract.ofCoordinates b cG).prod rq.model
  let U := matrixDenote (solvePresentedStage data hs).value.1
  let V := matrixDenote (solvePresentedStage data hs).value.2.1
  have he := solvePresentedStage_correct data hs
  dsimp only at he
  rw [hα,hβ,hD,hS,hT] at he
  have hu : (stageLeft f).comp (T.mapOfMatrix S U) = stageRight g e :=
    PresentedTarget.matrix_solution_lifts S T target _ _ α β U _ he.1
  have hv : (stageRight g e).comp (S.mapOfMatrix T V) = stageLeft f :=
    PresentedTarget.matrix_solution_lifts T S target _ _ β α V _ he.2.2.2.1
  have hU : T.mapMatrix S (T.mapOfMatrix S U) = U :=
    FiniteRetract.mapMatrix_mapOfMatrix_of_normalized _ _ _ he.2.1 he.2.2.1
  have hV : S.mapMatrix T (S.mapOfMatrix T V) = V :=
    FiniteRetract.mapMatrix_mapOfMatrix_of_normalized _ _ _ he.2.2.2.2.1 he.2.2.2.2.2
  let e' := representedStep f g e a b cF cG rp.model rq.model
    (T.mapOfMatrix S U) (S.mapOfMatrix T V) hu hv
  have ho := firstUpdate_correct EP EQ (solvePresentedStage data hs).value.1
    (solvePresentedStage data hs).value.2.1
  refine ⟨{
    M := ModuleCat.of _ (LinearMap.ker f)
    N := ModuleCat.of _ (LinearMap.ker g)
    P := ModuleCat.of _ (G₀ × Q)
    Q := ModuleCat.of _ (F₀ × P)
    m := ⟨cF.toLinearMap.comp (LinearMap.ker f).subtype,
      cF.injective.comp (LinearMap.ker f).injective_subtype⟩
    n := ⟨cG.toLinearMap.comp (LinearMap.ker g).subtype,
      cG.injective.comp (LinearMap.ker g).injective_subtype⟩
    left := ⟨T.embed,T.project,T.retract⟩
    right := ⟨S.embed,S.project,S.retract⟩
    leftResolution := hF
    rightResolution := hG
    equiv := e'
    left_eq := ?_
    right_eq := ?_
    forward_eq := ?_
    inverse_eq := ?_ }⟩
  · exact ho.1.trans (by rw [hEQ]; exact (free_prod_projector b cG rq.model).symm)
  · exact ho.2.1.trans (by rw [hEP]; exact (free_prod_projector a cF rp.model).symm)
  · change _ = stepForward a b p q (T.mapMatrix S (T.mapOfMatrix S U))
      (S.mapMatrix T (S.mapOfMatrix T V))
    rw [hU,hV]
    exact ho.2.2.1
  · change _ = stepInverse a b p q (T.mapMatrix S (T.mapOfMatrix S U))
      (S.mapMatrix T (S.mapOfMatrix T V))
    rw [hU,hV]
    exact ho.2.2.2

end Decoupling.HighDim.StableFree.Effective
