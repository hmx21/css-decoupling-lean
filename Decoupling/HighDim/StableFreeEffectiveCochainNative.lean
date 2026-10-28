import Decoupling.HighDim.StableFreeEffectiveCochainRun

/-!
# Native finite-complex C4 program with all intermediate construction inputs removed

The only semantic inputs describe the actual supplied original coordinates,
original differentials and computed native homotopy equivalence. IsGE 1 and
the true lower support bound supply the exact finite resolution internally.
The program extracts original-coordinate slices, counts the two required
homotopy negations, constructs the initial arrows, runs Schanuel, and returns
both actual stable-check lift matrices.
-/
namespace Decoupling.HighDim.StableFree.Effective.CochainProgram
open Matrix LaurentArithmetic ArithmeticCost HomologicalComplex
universe u
variable {K : Type u} [Field K] [DecidableEq K] {D h n m : ℕ}
  {C T : CochainComplex (ModuleCat.{u} (Laurent K D)) ℤ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Full native run. All proofs used by the solver are derived inside;
no Initial.Data, Realizes, finite-resolution model or stable map is an input. -/
def runNative (cC : StableFree.Coordinates C) (cT : StableFree.Coordinates T)
    (frameC : AlgorithmTwoFiniteComplex.Coordinates C n) (frameT : AlgorithmTwoFiniteComplex.Coordinates T m)
    (sC : TermSelectors cC.rank n) (sT : TermSelectors cT.rank m)
    (hC : FrameRealizes cC frameC sC) (hT : FrameRealizes cT frameT sT)
    (e : HomotopyEquiv C T) (arrays : NativeArrays K D n m h)
    (ha : NativeRealizes frameC frameT e arrays) (l : ℕ)
    [C.IsGE 1] [T.IsGE 1] [C.IsStrictlyGE (-(l:ℤ))] [T.IsStrictlyGE (-(l:ℤ))] :=
  let extracted := extractInputs sC sT arrays
  let i := extracted.value
  let F := tailTower sT arrays.differentialT (l+1)
  let G := tailTower sC arrays.differentialC (l+1)
  have hi := extractInputs_realizes cC cT frameC frameT sC sT hC hT e arrays ha
  have hF := tailTower_models cT frameT sT hT arrays.differentialT ha.differentialT l
  have hG := tailTower_models cC frameC sC hC arrays.differentialC ha.differentialC l
  Work.bind extracted fun _ => runInitial i F G (by dsimp [Initial.radius5,Initial.radius4,Initial.radius3,Initial.radius2]; omega)
    (initialStage_solvable i (Initial.homotopyData e cC cT) hi)
    (initialStage_valid i (Initial.homotopyData e cC cT) hi F G hF hG)

/-- Both returned matrices represent the actual native stable-check beta. -/
theorem runNative_presents (cC : StableFree.Coordinates C) (cT : StableFree.Coordinates T)
    (frameC : AlgorithmTwoFiniteComplex.Coordinates C n) (frameT : AlgorithmTwoFiniteComplex.Coordinates T m)
    (sC : TermSelectors cC.rank n) (sT : TermSelectors cT.rank m)
    (hC : FrameRealizes cC frameC sC) (hT : FrameRealizes cT frameT sT)
    (e : HomotopyEquiv C T) (arrays : NativeArrays K D n m h)
    (ha : NativeRealizes frameC frameT e arrays) (l : ℕ)
    [C.IsGE 1] [T.IsGE 1] [C.IsStrictlyGE (-(l:ℤ))] [T.IsStrictlyGE (-(l:ℤ))] :
    let F := tailTower sT arrays.differentialT (l+1)
    let G := tailTower sC arrays.differentialC (l+1)
    let πC := ((LinearMap.range (C.d 0 1).hom).mkQ).comp (cC.equiv 1).symm.toLinearMap
    let πT := ((LinearMap.range (T.d 0 1).hom).mkQ).comp (cT.equiv 1).symm.toLinearMap
    ∃ beta : (CochainCokernel.CheckCokernel T × Power (Laurent K D) (cC.rank 2+(cC.rank 1+(F.ranks G).1)))
        ≃ₗ[Laurent K D] (CochainCokernel.CheckCokernel C ×
          Power (Laurent K D) (cC.rank 2+(cT.rank 1+(F.ranks G).2))),
      (∀ x, stabilizedQuotient (N := ModuleCat.of (Laurent K D) (CochainCokernel.CheckCokernel C)) πC _
        (matrixDenote (runNative cC cT frameC frameT sC sT hC hT e arrays ha l).value.forward *ᵥ x) =
          beta (stabilizedQuotient (N := ModuleCat.of (Laurent K D) (CochainCokernel.CheckCokernel T)) πT _ x)) ∧
      (∀ x, stabilizedQuotient (N := ModuleCat.of (Laurent K D) (CochainCokernel.CheckCokernel T)) πT _
        (matrixDenote (runNative cC cT frameC frameT sC sT hC hT e arrays ha l).value.inverse *ᵥ x) =
          beta.symm (stabilizedQuotient (N := ModuleCat.of (Laurent K D) (CochainCokernel.CheckCokernel C)) πC _ x)) := by
  have hπC : (Initial.homotopyData e cC cT).piM =
      ((LinearMap.range (C.d 0 1).hom).mkQ).comp (cC.equiv 1).symm.toLinearMap := rfl
  have hπT : (Initial.homotopyData e cC cT).piN =
      ((LinearMap.range (T.d 0 1).hom).mkQ).comp (cT.equiv 1).symm.toLinearMap := rfl
  simpa only [runNative,Work.bind_value,hπC,hπT] using (runInitial_presents
    (M := ModuleCat.of (Laurent K D) (CochainCokernel.CheckCokernel C))
    (N := ModuleCat.of (Laurent K D) (CochainCokernel.CheckCokernel T)) (extractInputs sC sT arrays).value (Initial.homotopyData e cC cT)
    (extractInputs_realizes cC cT frameC frameT sC sT hC hT e arrays ha)
    (tailTower sT arrays.differentialT (l+1)) (tailTower sC arrays.differentialC (l+1))
    (tailTower_models cT frameT sT hT arrays.differentialT ha.differentialT l)
    (tailTower_models cC frameC sC hC arrays.differentialC ha.differentialC l)
    (by dsimp [Initial.radius5,Initial.radius4,Initial.radius3,Initial.radius2]; omega))

end Decoupling.HighDim.StableFree.Effective.CochainProgram
