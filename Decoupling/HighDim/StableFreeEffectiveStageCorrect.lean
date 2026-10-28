import Decoupling.HighDim.StableFreeEffectiveStageProgram

/-!
# Semantic correctness of the actual two-solve stage

Solvability follows from actual free covers and the explicitly represented
projective factors. Each returned matrix determines an actual module lift;
the normalized equations identify its stored matrix with that very lift.
-/

namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic
universe u
variable {K : Type u} [Field K] {D h h₀ length s t a b p q : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Actual state validity discharges both lifting problems. -/
theorem prepareStage_solvable (A : DenseMatrix K D s a h₀) (B : DenseMatrix K D t b h₀)
    (F : DenseTower K D h₀ length a) (G : DenseTower K D h₀ length b)
    (data : EmbeddedArrays K D s t p q h) (hh : h₀ ≤ h)
    (hv : StateValid (.step a A F) (.step b B G) data) :
    (prepareStage A B data).value.Solvable := by
  obtain ⟨w⟩ := hv
  cases w.leftResolution with
  | step F₀ cF f hf hA hF =>
    cases w.rightResolution with
    | step G₀ cG g hg hB hG =>
      let S := (FiniteRetract.ofCoordinates a cF).prod w.left.model
      let T := (FiniteRetract.ofCoordinates b cG).prod w.right.model
      let target := embeddedTarget w.m.model w.left.model
      let α := embeddedLeftArrow w.m.model w.left.model a cF f
      let β := embeddedRightArrow w.m.model w.n.model w.left.model w.right.model w.equiv b cG g
      have hsU := PresentedTarget.lift_system_solvable S T target
        (stageLeft f) (stageRight g w.equiv.equiv) α β (stageLeft_surjective f hf)
      have hsV := PresentedTarget.lift_system_solvable T S target
        (stageRight g w.equiv.equiv) (stageLeft f) β α (stageRight_surjective g hg _)
      have hp := prepareStage_correct A B data hh
      rcases hp with ⟨hpA,hpB,hpS,hpT⟩
      unfold StageArrays.Solvable
      rw [hpA,hpB,hpS,hpT,w.left_eq,w.right_eq,w.inverse_eq,hA,hB]
      constructor
      · with_unfolding_all simpa only [S,T,target,α,β,embeddedLeftArrow,embeddedRightArrow,
          embeddedTarget_relations,free_prod_projector,coverMatrix,EmbeddingAt.model,
          embeddedTarget_size,embeddedTarget_relationCount,free_prod_size] using hsU
      · with_unfolding_all simpa only [S,T,target,α,β,embeddedLeftArrow,embeddedRightArrow,
          embeddedTarget_relations,free_prod_projector,coverMatrix,EmbeddingAt.model,
          embeddedTarget_size,embeddedTarget_relationCount,free_prod_size] using hsV

variable [DecidableEq K]

/-- The matrix program constructs the next actual syzygy state. -/
theorem updateStage_valid (A : DenseMatrix K D s a h₀) (B : DenseMatrix K D t b h₀)
    (F : DenseTower K D h₀ length a) (G : DenseTower K D h₀ length b)
    (data : EmbeddedArrays K D s t p q h) (hh : h₀ ≤ h)
    (hv : StateValid (.step a A F) (.step b B G) data)
    (hs : (prepareStage A B data).value.Solvable) :
    StateValid F G (updateStage data (solveStage (prepareStage A B data).value hs).value.1
      (solveStage (prepareStage A B data).value hs).value.2).value := by
  obtain ⟨w⟩ := hv
  cases w.leftResolution with
  | step F₀ cF f hf hA hF =>
    cases w.rightResolution with
    | step G₀ cG g hg hB hG =>
      let S := (FiniteRetract.ofCoordinates a cF).prod w.left.model
      let T := (FiniteRetract.ofCoordinates b cG).prod w.right.model
      let target := embeddedTarget w.m.model w.left.model
      let α := embeddedLeftArrow w.m.model w.left.model a cF f
      let β := embeddedRightArrow w.m.model w.n.model w.left.model w.right.model w.equiv b cG g
      let U : Matrix (Fin (a+p)) (Fin (b+q)) (Laurent K D) := matrixDenote (solveStage (prepareStage A B data).value hs).value.1
      let V : Matrix (Fin (b+q)) (Fin (a+p)) (Laurent K D) := matrixDenote (solveStage (prepareStage A B data).value hs).value.2
      have hp := prepareStage_correct A B data hh
      rcases hp with ⟨hpA,hpB,hpS,hpT⟩
      have he := solveStage_correct (prepareStage A B data).value hs
      dsimp only at he
      rw [hpA,hpB,hpS,hpT,w.left_eq,w.right_eq,w.inverse_eq,hA,hB] at he
      have hu : (stageLeft f).comp (T.mapOfMatrix S U) = stageRight g w.equiv.equiv := by
        apply PresentedTarget.matrix_solution_lifts S T target _ _ α β U 0
        rw [embeddedTarget_relations,Matrix.zero_mul,sub_eq_zero]
        exact he.1
      have hv' : (stageRight g w.equiv.equiv).comp (S.mapOfMatrix T V) = stageLeft f := by
        apply PresentedTarget.matrix_solution_lifts T S target _ _ β α V 0
        rw [embeddedTarget_relations,Matrix.zero_mul,sub_eq_zero]
        exact he.2.2.2.1
      have hU : T.mapMatrix S (T.mapOfMatrix S U) = U := by
        apply FiniteRetract.mapMatrix_mapOfMatrix_of_normalized
        · simpa only [S,free_prod_projector] using he.2.1
        · simpa only [T,free_prod_projector] using he.2.2.1
      have hV : S.mapMatrix T (S.mapOfMatrix T V) = V := by
        apply FiniteRetract.mapMatrix_mapOfMatrix_of_normalized
        · simpa only [T,free_prod_projector] using he.2.2.2.2.1
        · simpa only [S,free_prod_projector] using he.2.2.2.2.2
      let e' := representedStep f g w.equiv.equiv a b cF cG w.left.model w.right.model
        (T.mapOfMatrix S U) (S.mapOfMatrix T V) hu hv'
      have ho := updateStage_correct data (solveStage (prepareStage A B data).value hs).value.1
        (solveStage (prepareStage A B data).value hs).value.2
      refine ⟨{
        M := ModuleCat.of _ (LinearMap.ker f)
        N := ModuleCat.of _ (LinearMap.ker g)
        P := ModuleCat.of _ (G₀ × w.Q)
        Q := ModuleCat.of _ (F₀ × w.P)
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
      · exact ho.1.trans (by rw [w.right_eq]; exact (free_prod_projector b cG w.right.model).symm)
      · exact ho.2.1.trans (by rw [w.left_eq]; exact (free_prod_projector a cF w.left.model).symm)
      · change _ = stepForward a b p q (T.mapMatrix S (T.mapOfMatrix S U))
          (S.mapMatrix T (S.mapOfMatrix T V))
        rw [hU,hV]
        exact ho.2.2.1
      · change _ = stepInverse a b p q (T.mapMatrix S (T.mapOfMatrix S U))
          (S.mapMatrix T (S.mapOfMatrix T V))
        rw [hU,hV]
        exact ho.2.2.2

end Decoupling.HighDim.StableFree.Effective
