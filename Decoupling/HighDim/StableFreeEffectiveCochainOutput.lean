import Decoupling.HighDim.StableFreeEffectiveCochainCost
import Decoupling.HighDim.StableFreeEffectiveCochainRelations

/-!
# Complete native C4 output for the four comparison systems

Both actual stable relation matrices and the two computed quotient lifts
are materialized in the same explicit coefficient box. Appended zero rows,
coordinate selection and padding only copy coefficients and add no field
operations. The output theorem gives precisely the real augmented
presentation and beta equations consumed by fromPresentationsProgram.
-/
namespace Decoupling.HighDim.StableFree.Effective.CochainProgram
open Matrix LaurentArithmetic ArithmeticCost HomologicalComplex
universe u
variable {K : Type u} [Field K] [DecidableEq K] {D h n m : ℕ}
  {C T : CochainComplex (ModuleCat.{u} (Laurent K D)) ℤ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

structure Output (K : Type u) (D c1 c0 t1 t0 extraC extraT H : ℕ) where
  dC : DenseMatrix K D (c1+extraC) c0 H
  dT : DenseMatrix K D (t1+extraT) t0 H
  forward : DenseMatrix K D (c1+extraC) (t1+extraT) H
  inverse : DenseMatrix K D (t1+extraT) (c1+extraC) H

def execute (cC : StableFree.Coordinates C) (cT : StableFree.Coordinates T)
    (frameC : AlgorithmTwoFiniteComplex.Coordinates C n) (frameT : AlgorithmTwoFiniteComplex.Coordinates T m)
    (sC : TermSelectors cC.rank n) (sT : TermSelectors cT.rank m)
    (hC : FrameRealizes cC frameC sC) (hT : FrameRealizes cT frameT sT)
    (e : HomotopyEquiv C T) (arrays : NativeArrays K D n m h)
    (ha : NativeRealizes frameC frameT e arrays) (l : ℕ)
    [C.IsGE 1] [T.IsGE 1] [C.IsStrictlyGE (-(l:ℤ))] [T.IsStrictlyGE (-(l:ℤ))] :
    let F := tailTower sT arrays.differentialT (l+1)
    let G := tailTower sC arrays.differentialC (l+1)
    Work K (Output K D (cC.rank 1) (cC.rank 0) (cT.rank 1) (cT.rank 0)
      (cC.rank 2+(cT.rank 1+(F.ranks G).2)) (cC.rank 2+(cC.rank 1+(F.ranks G).1))
      (runBox F G (cC.rank 2) (cT.rank 2) h)) :=
  Work.bind (runNative cC cT frameC frameT sC sT hC hT e arrays ha l) fun beta => Work.pure {
    dC := augmentedRelations sC arrays.differentialC _ _
    dT := augmentedRelations sT arrays.differentialT _ _
    forward := beta.forward
    inverse := beta.inverse }

/-- Exact native presentations and original-coordinate beta representatives.
All four equations concern the actual returned dense arrays. -/
theorem execute_correct (cC : StableFree.Coordinates C) (cT : StableFree.Coordinates T)
    (frameC : AlgorithmTwoFiniteComplex.Coordinates C n) (frameT : AlgorithmTwoFiniteComplex.Coordinates T m)
    (sC : TermSelectors cC.rank n) (sT : TermSelectors cT.rank m)
    (hC : FrameRealizes cC frameC sC) (hT : FrameRealizes cT frameT sT)
    (e : HomotopyEquiv C T) (arrays : NativeArrays K D n m h)
    (ha : NativeRealizes frameC frameT e arrays) (l : ℕ)
    [C.IsGE 1] [T.IsGE 1] [C.IsStrictlyGE (-(l:ℤ))] [T.IsStrictlyGE (-(l:ℤ))] :
    let F := tailTower sT arrays.differentialT (l+1)
    let G := tailTower sC arrays.differentialC (l+1)
    let extraC := cC.rank 2+(cT.rank 1+(F.ranks G).2)
    let extraT := cC.rank 2+(cC.rank 1+(F.ranks G).1)
    let piC := stabilizedQuotient (N := ModuleCat.of (Laurent K D) (CochainCokernel.CheckCokernel C))
      (checkQuotient cC) extraC
    let piT := stabilizedQuotient (N := ModuleCat.of (Laurent K D) (CochainCokernel.CheckCokernel T))
      (checkQuotient cT) extraT
    let out := (execute cC cT frameC frameT sC sT hC hT e arrays ha l).value
    ∃ beta : (CochainCokernel.CheckCokernel T × Power (Laurent K D) extraT)
        ≃ₗ[Laurent K D] (CochainCokernel.CheckCokernel C × Power (Laurent K D) extraC),
      LinearMap.range (matrixDenote out.dC).mulVecLin = LinearMap.ker piC ∧
      LinearMap.range (matrixDenote out.dT).mulVecLin = LinearMap.ker piT ∧
      piC.comp (matrixDenote out.forward).mulVecLin = beta.toLinearMap.comp piT ∧
      piT.comp (matrixDenote out.inverse).mulVecLin = beta.symm.toLinearMap.comp piC := by
  dsimp only
  obtain ⟨beta,hF,hG⟩ := runNative_presents cC cT frameC frameT sC sT hC hT e arrays ha l
  refine ⟨beta,?_,?_,?_,?_⟩
  · exact (augmentedRelations_kernel cC frameC sC hC arrays.differentialC ha.differentialC _
      (runBox_ge_input _ _ _ _ _)).symm
  · exact (augmentedRelations_kernel cT frameT sT hT arrays.differentialT ha.differentialT _
      (runBox_ge_input _ _ _ _ _)).symm
  · apply LinearMap.ext
    exact hF
  · apply LinearMap.ext
    exact hG

theorem execute_cost (cC : StableFree.Coordinates C) (cT : StableFree.Coordinates T)
    (frameC : AlgorithmTwoFiniteComplex.Coordinates C n) (frameT : AlgorithmTwoFiniteComplex.Coordinates T m)
    (sC : TermSelectors cC.rank n) (sT : TermSelectors cT.rank m)
    (hC : FrameRealizes cC frameC sC) (hT : FrameRealizes cT frameT sT)
    (e : HomotopyEquiv C T) (arrays : NativeArrays K D n m h)
    (ha : NativeRealizes frameC frameT e arrays) (l : ℕ)
    [C.IsGE 1] [T.IsGE 1] [C.IsStrictlyGE (-(l:ℤ))] [T.IsStrictlyGE (-(l:ℤ))] :
    (execute cC cT frameC frameT sC sT hC hT e arrays ha l).cost ≤
      (cC.rank 1*cC.rank 2+cT.rank 1*cT.rank 2)*boxSize D h +
      (completeInitialCost D (cC.rank 1) (cT.rank 1) (cC.rank 2) (cT.rank 2) h +
        remainingCost (tailTower sT arrays.differentialT (l+1)) (tailTower sC arrays.differentialC (l+1))
          (cC.rank 2) (cT.rank 2) (cT.rank 0) h) := by
  rw [execute,Work.bind_cost,Work.pure_cost,add_zero]
  exact runNative_cost cC cT frameC frameT sC sT hC hT e arrays ha l

end Decoupling.HighDim.StableFree.Effective.CochainProgram
