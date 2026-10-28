import Decoupling.HighDim.StableFreeEffectiveCochainOutput

/-! # Executable C4 engine whose inputs contain arrays and proof-only validity

Native homotopy equivalences do not occur among runtime arguments. The
readiness proposition is proved from the solved cone in the pipeline.
The engine is definitionally the native C4 program, with identical arrays
and operation trace; no replacement inverse or presentation is selected.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipeline
open Matrix LaurentArithmetic ArithmeticCost HomologicalComplex
open StableFree.Effective StableFree.Effective.CochainProgram
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D h n m : ℕ}
variable {rC rT : ℤ → ℕ}

/-- All solver premises needed by the data-only C4 engine, in `Prop`. -/
def C4Ready (sC : TermSelectors rC n) (sT : TermSelectors rT m)
    (arrays : NativeArrays K D n m h) (l : ℕ) : Prop :=
  let i := (extractInputs sC sT arrays).value
  let F := tailTower sT arrays.differentialT (l+1)
  let G := tailTower sC arrays.differentialC (l+1)
  ∃ hs : (initialStage i.runComplete.value.initial).Solvable,
    StateValid F G (firstUpdate (identityDense K D (Initial.radius5 h) (rC 2))
      i.runComplete.value.initial.complementProjector
      (solvePresentedStage (initialStage i.runComplete.value.initial) hs).value.1
      (solvePresentedStage (initialStage i.runComplete.value.initial) hs).value.2.1).value

/-- Exactly one extraction and one C4 run, with only materialized data inputs. -/
def c4DataProgram (sC : TermSelectors rC n) (sT : TermSelectors rT m)
    (arrays : NativeArrays K D n m h) (l : ℕ) (ready : C4Ready sC sT arrays l) :
    let F := tailTower sT arrays.differentialT (l+1)
    let G := tailTower sC arrays.differentialC (l+1)
    Work K (Output K D (rC 1) (rC 0) (rT 1) (rT 0)
      (rC 2+(rT 1+(F.ranks G).2)) (rC 2+(rC 1+(F.ranks G).1))
      (runBox F G (rC 2) (rT 2) h)) :=
  let extracted := extractInputs sC sT arrays
  let i := extracted.value
  let F := tailTower sT arrays.differentialT (l+1)
  let G := tailTower sC arrays.differentialC (l+1)
  have hs := Classical.choose ready
  have hv := Classical.choose_spec ready
  Work.bind (Work.bind extracted fun _ => runInitial i F G
    (by dsimp [Initial.radius5,Initial.radius4,Initial.radius3,Initial.radius2]; omega) hs hv)
    fun beta => Work.pure {
      dC := augmentedRelations sC arrays.differentialC _ _
      dT := augmentedRelations sT arrays.differentialT _ _
      forward := beta.forward
      inverse := beta.inverse }

noncomputable section
variable {C T : CochainComplex (ModuleCat (Laurent K D)) ℤ}

/-- The native semantics discharge readiness; no readiness premise survives. -/
theorem c4Ready_of_native (cC : StableFree.Coordinates C) (cT : StableFree.Coordinates T)
    (frameC : AlgorithmTwoFiniteComplex.Coordinates C n) (frameT : AlgorithmTwoFiniteComplex.Coordinates T m)
    (sC : TermSelectors cC.rank n) (sT : TermSelectors cT.rank m)
    (hC : FrameRealizes cC frameC sC) (hT : FrameRealizes cT frameT sT)
    (e : HomotopyEquiv C T) (arrays : NativeArrays K D n m h)
    (ha : NativeRealizes frameC frameT e arrays) (l : ℕ)
    [C.IsGE 1] [T.IsGE 1] [C.IsStrictlyGE (-(l:ℤ))] [T.IsStrictlyGE (-(l:ℤ))] :
    C4Ready sC sT arrays l := by
  have hi := extractInputs_realizes cC cT frameC frameT sC sT hC hT e arrays ha
  have hF := tailTower_models cT frameT sT hT arrays.differentialT ha.differentialT l
  have hG := tailTower_models cC frameC sC hC arrays.differentialC ha.differentialC l
  exact ⟨initialStage_solvable _ (Initial.homotopyData e cC cT) hi,
    initialStage_valid _ (Initial.homotopyData e cC cT) hi _ _ hF hG⟩

/-- Equality includes the complete operation trace, not only the output value. -/
theorem c4DataProgram_eq_execute (cC : StableFree.Coordinates C) (cT : StableFree.Coordinates T)
    (frameC : AlgorithmTwoFiniteComplex.Coordinates C n) (frameT : AlgorithmTwoFiniteComplex.Coordinates T m)
    (sC : TermSelectors cC.rank n) (sT : TermSelectors cT.rank m)
    (hC : FrameRealizes cC frameC sC) (hT : FrameRealizes cT frameT sT)
    (e : HomotopyEquiv C T) (arrays : NativeArrays K D n m h)
    (ha : NativeRealizes frameC frameT e arrays) (l : ℕ)
    [C.IsGE 1] [T.IsGE 1] [C.IsStrictlyGE (-(l:ℤ))] [T.IsStrictlyGE (-(l:ℤ))]
    (ready : C4Ready sC sT arrays l) :
    c4DataProgram sC sT arrays l ready = execute cC cT frameC frameT sC sT hC hT e arrays ha l := rfl

end
end Decoupling.HighDim.AlgorithmTwoPipeline
