import Decoupling.HighDim.StableFreeEffectiveCochainFrame
import Decoupling.HighDim.StableFreeEffectiveCochainInitial

/-!
# Actual seven initial matrices extracted from the native homotopy arrays

Original-term selectors copy Γ¹, Δ¹, d¹ and d⁰. The two homotopy blocks
are negated by actual counted arithmetic, because Initial.homotopyData uses
the reversed homotopies. No characteristic-two sign cancellation is used.
-/
namespace Decoupling.HighDim.StableFree.Effective.CochainProgram
open Matrix LaurentArithmetic ArithmeticCost HomologicalComplex
universe u
variable {K : Type u} [Field K] {D h n m : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

structure NativeArrays (K : Type u) (D n m h : ℕ) where
  differentialC : DenseMatrix K D n n h
  differentialT : DenseMatrix K D m m h
  hom : DenseMatrix K D m n h
  inv : DenseMatrix K D n m h
  homotopyC : DenseMatrix K D n n h
  homotopyT : DenseMatrix K D m m h

def extractInputs {rC rT : ℤ → ℕ} (sC : TermSelectors rC n) (sT : TermSelectors rT m)
    (arrays : NativeArrays K D n m h) :
    Work K (Initial.Inputs K D (rC 1) (rT 1) (rC 2) (rT 2) (rT 0) h) :=
  Work.bind (matrixNegProgram (originalSlice sC sC 1 2 arrays.homotopyC)) fun Z =>
    Work.bind (matrixNegProgram (originalSlice sT sT 1 2 arrays.homotopyT)) fun T => Work.pure {
      F := originalSlice sT sC 1 1 arrays.hom
      G := originalSlice sC sT 1 1 arrays.inv
      X := originalSlice sC sC 2 1 arrays.differentialC
      Y := originalSlice sT sT 2 1 arrays.differentialT
      Z := Z
      T := T
      relations := originalSlice sT sT 1 0 arrays.differentialT }

theorem extractInputs_cost {rC rT : ℤ → ℕ} (sC : TermSelectors rC n) (sT : TermSelectors rT m)
    (arrays : NativeArrays K D n m h) :
    (extractInputs sC sT arrays).cost = (rC 1*rC 2+rT 1*rT 2)*boxSize D h := by
  simp only [extractInputs,Work.bind_cost,Work.pure_cost,add_zero,matrixNegProgram_cost]
  ring

noncomputable section
variable {C T : CochainComplex (ModuleCat.{u} (Laurent K D)) ℤ}

/-- Actual representation of the computed native homotopy equivalence and
original differentials in their supplied total coordinate frames. -/
structure NativeRealizes (frameC : AlgorithmTwoFiniteComplex.Coordinates C n)
    (frameT : AlgorithmTwoFiniteComplex.Coordinates T m)
    (e : HomotopyEquiv C T) (arrays : NativeArrays K D n m h) : Prop where
  differentialC : frameC.RepresentsDifferential (matrixDenote arrays.differentialC)
  differentialT : frameT.RepresentsDifferential (matrixDenote arrays.differentialT)
  hom : ∀ j x, matrixDenote arrays.hom *ᵥ frameC.embed j x = frameT.embed j ((e.hom.f j).hom x)
  inv : ∀ j x, matrixDenote arrays.inv *ᵥ frameT.embed j x = frameC.embed j ((e.inv.f j).hom x)
  homotopyC : ∀ a b, b+1=a → ∀ x,
    matrixDenote arrays.homotopyC *ᵥ frameC.embed a x = frameC.embed b ((e.homotopyHomInvId.hom a b).hom x)
  homotopyT : ∀ a b, b+1=a → ∀ x,
    matrixDenote arrays.homotopyT *ᵥ frameT.embed a x = frameT.embed b ((e.homotopyInvHomId.hom a b).hom x)

/-- Every initial input coefficient is the corresponding actual native
matrix, with the reversed-homotopy signs proved rather than assumed. -/
theorem extractInputs_realizes (cC : StableFree.Coordinates C) (cT : StableFree.Coordinates T)
    (frameC : AlgorithmTwoFiniteComplex.Coordinates C n) (frameT : AlgorithmTwoFiniteComplex.Coordinates T m)
    (sC : TermSelectors cC.rank n) (sT : TermSelectors cT.rank m)
    (hC : FrameRealizes cC frameC sC) (hT : FrameRealizes cT frameT sT)
    (e : HomotopyEquiv C T) (arrays : NativeArrays K D n m h)
    (ha : NativeRealizes frameC frameT e arrays) :
    Initial.Realizes (extractInputs sC sT arrays).value (Initial.homotopyData e cC cT) := by
  constructor
  · exact originalSlice_native cT cC frameT frameC sT sC hT hC 1 1 arrays.hom _ (ha.hom 1)
  · exact originalSlice_native cC cT frameC frameT sC sT hC hT 1 1 arrays.inv _ (ha.inv 1)
  · exact originalSlice_native cC cC frameC frameC sC sC hC hC 2 1 arrays.differentialC _
      (AlgorithmTwoFiniteComplex.represents_at frameC _ ha.differentialC 1 2 rfl)
  · exact originalSlice_native cT cT frameT frameT sT sT hT hT 2 1 arrays.differentialT _
      (AlgorithmTwoFiniteComplex.represents_at frameT _ ha.differentialT 1 2 rfl)
  · change matrixDenote (matrixNegProgram (originalSlice sC sC 1 2 arrays.homotopyC)).value = _
    rw [matrixNegProgram_correct,originalSlice_native cC cC frameC frameC sC sC hC hC 1 2
      arrays.homotopyC _ (ha.homotopyC 2 1 rfl)]
    apply Matrix.mulVec_injective
    funext x
    rw [Matrix.neg_mulVec,LinearMap.toMatrix'_mulVec]
    change -(cC.equiv 1 ((e.homotopyHomInvId.hom 2 1).hom ((cC.equiv 2).symm x))) =
      LinearMap.toMatrix' (Initial.homotopyData e cC cT).Z *ᵥ x
    rw [LinearMap.toMatrix'_mulVec]
    change _ = cC.equiv 1 (-((e.homotopyHomInvId.hom 2 1).hom ((cC.equiv 2).symm x)))
    rw [map_neg]
  · change matrixDenote (matrixNegProgram (originalSlice sT sT 1 2 arrays.homotopyT)).value = _
    rw [matrixNegProgram_correct,originalSlice_native cT cT frameT frameT sT sT hT hT 1 2
      arrays.homotopyT _ (ha.homotopyT 2 1 rfl)]
    apply Matrix.mulVec_injective
    funext x
    rw [Matrix.neg_mulVec,LinearMap.toMatrix'_mulVec]
    change -(cT.equiv 1 ((e.homotopyInvHomId.hom 2 1).hom ((cT.equiv 2).symm x))) =
      LinearMap.toMatrix' (Initial.homotopyData e cC cT).T *ᵥ x
    rw [LinearMap.toMatrix'_mulVec]
    change _ = cT.equiv 1 (-((e.homotopyInvHomId.hom 2 1).hom ((cT.equiv 2).symm x)))
    rw [map_neg]
  · exact originalSlice_native cT cT frameT frameT sT sT hT hT 1 0 arrays.differentialT _
      (AlgorithmTwoFiniteComplex.represents_at frameT _ ha.differentialT 0 1 rfl)

end
end Decoupling.HighDim.StableFree.Effective.CochainProgram
