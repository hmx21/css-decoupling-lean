import Decoupling.HighDim.AlgorithmTwoToricDataDifferential
import Decoupling.HighDim.AlgorithmTwoToricDataTop
import Decoupling.HighDim.AlgorithmTwoComparisonBounds

/-!
# Complete operational toric target from the stored multiplicities

The input is a materialised natural-number vector. The output arrays
are the actual toric differential and the actual empty-cell columns,
in explicit finite integer-mask coordinates. The native bridge,
degree bounds, rank formula, and actual field-operation count are
all proved here without coordinate or solver certificates.
-/
namespace Decoupling.HighDim.AlgorithmTwoToricData
open CategoryTheory HomologicalComplex LaurentArithmetic AlgorithmTwoFiniteComplex
open AlgorithmTwoComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
variable (D : ℕ) (t : Vector ℕ (D - 1)) (K : Type) [Field K]

theorem nativeStack_bounds :
    (nativeStack D t K).IsStrictlyGE (-(D : ℤ)) ∧
      (nativeStack D t K).IsStrictlyLE (D : ℤ) :=
  stack_dimension_bounds K D (Toric.copyForms D (multiplicities D t)) (by
    intro i
    have hi := i.1.isLt
    change i.1.val + 1 ≤ D
    omega)

/-- Every executed output is identified with the actual native object,
and its actual trace contains precisely one field operation. -/
theorem targetProgram_spec :
    (totalCoordinates D t K).RepresentsDifferential (matrixDenote (targetProgram (K := K) D t).value.1) ∧
      Homogeneous (degrees D t) (degrees D t) 1 (matrixDenote (targetProgram (K := K) D t).value.1) ∧
      (∀ c : Fin (copyCount D t),
        (matrixDenote (targetProgram (K := K) D t).value.2).col c =
          (totalCoordinates D t K).embed (((copyEquiv D t c).1.val : ℤ) + 1)
            (stackTop K D (Toric.copyForms D (multiplicities D t)) (copyEquiv D t c))) ∧
      (targetProgram (K := K) D t).cost = 1 := by
  refine ⟨?_, ?_, ?_, targetProgram_cost D t⟩
  · change (totalCoordinates D t K).RepresentsDifferential
      (matrixDenote (differentialArray D t (-1 : K)))
    rw [differentialArray_native]
    exact differentialMatrix_represents _
  · exact differentialArray_homogeneous D t
  · intro c
    exact topProgram_native D t K c

end
end Decoupling.HighDim.AlgorithmTwoToricData
