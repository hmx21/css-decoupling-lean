import Decoupling.HighDim.AlgorithmTwoToricDataCoefficients
import Decoupling.HighDim.AlgorithmTwoFiniteComplexCoordinates

/-! # The executed differential array has degree one -/
namespace Decoupling.HighDim.AlgorithmTwoToricData
open LaurentArithmetic AlgorithmTwoFiniteComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
variable {K : Type} [Field K] (D : ℕ) (t : Vector ℕ (D - 1))

theorem differentialArray_entry (r c : Fin (totalRank D t)) :
    matrixDenote (differentialArray D t (-1 : K)) r c =
      if (labelEquiv D t r).1 = (labelEquiv D t c).1 then
        denote (faceDense (-1 : K) (subsetAt D (labelEquiv D t r).2) (subsetAt D (labelEquiv D t c).2))
      else 0 := by
  simp only [matrixDenote, differentialArray, Fin.getElem_fin, Vector.getElem_ofFn]
  split_ifs
  · rfl
  · simp [denote]

theorem differentialArray_homogeneous :
    Homogeneous (degrees D t) (degrees D t) 1 (matrixDenote (differentialArray D t (-1 : K))) := by
  intro r c hn
  rw [differentialArray_entry]
  split_ifs with hc
  · cases he : removedDirection (subsetAt D (labelEquiv D t r).2)
        (subsetAt D (labelEquiv D t c).2) with
    | none => exact faceDense_none he
    | some i =>
      have hh := removedDirection_card he
      have hform := congrArg (fun x : Copy D t => x.1.val) hc
      simp only [degrees_get, labelDegree] at hn
      exact False.elim (hn (by omega))
  · rfl

theorem differentialArray_supported :
    LaurentBoxes.MatrixSupported (matrixDenote (differentialArray D t (-1 : K))) 1 :=
  fun _ _ => denote_supported _

end
end Decoupling.HighDim.AlgorithmTwoToricData
