import Decoupling.HighDim.AlgorithmTwoToricDataProgram

/-!
# Exact Laurent meaning of the cached-sign face arrays

The actual radius-one dense coefficients denote the signed coordinate
difference. This connects the lookup program to the Laurent ring,
including the constant coefficient and all odd-characteristic signs.
-/
namespace Decoupling.HighDim.AlgorithmTwoToricData
open LaurentArithmetic
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
variable {K : Type} [Field K] {D : ℕ}

theorem unitExponent_ne_zero (i : Fin D) : unitExponent D i ≠ 0 := by
  intro he
  have hi := congrFun he i
  simp [unitExponent] at hi

theorem unitExponent_mem_box (i : Fin D) : unitExponent D i ∈ LaurentBoxes.box D 1 := by
  rw [LaurentBoxes.mem_box]
  intro j
  by_cases hji : j = i <;> simp [unitExponent, hji]

def signedDifference (i : Fin D) (s : K) : Laurent K D :=
  AddMonoidAlgebra.single (unitExponent D i) s + AddMonoidAlgebra.single 0 (-s)

theorem signedDifference_eq (i : Fin D) (s : K) :
    signedDifference i s = constant s * difference K i := by
  simp [signedDifference, constant, difference, coordinate, monomial,
    unitExponent_eq, mul_add, sub_eq_add_neg]

theorem signedDifference_supported (i : Fin D) (s : K) :
    LaurentBoxes.Supported (signedDifference i s) 1 := by
  intro a ha
  by_cases hei : a = unitExponent D i
  · subst a
    exact unitExponent_mem_box i
  · by_cases hz : a = 0
    · subst a
      simp [LaurentBoxes.mem_box]
    · have hc : (signedDifference i s).coeff a = 0 := by
        simp [signedDifference, AddMonoidAlgebra.coeff_add, AddMonoidAlgebra.coeff_single,
          Ne.symm hei, Ne.symm hz]
      exact False.elim (Finsupp.mem_support_iff.mp ha hc)

theorem faceCoefficient_some {row col : Finset (Fin D)} {i : Fin D}
    (he : removedDirection row col = some i) (a : Translation D) :
    faceCoefficient (-1 : K) row col a =
      (signedDifference i (cachedSign (-1 : K) (cellPosition col i))).coeff a := by
  have hi := unitExponent_ne_zero i
  by_cases hei : a = unitExponent D i
  · subst a
    simp [faceCoefficient, he, signedDifference, AddMonoidAlgebra.coeff_add,
      AddMonoidAlgebra.coeff_single, Ne.symm hi]
  · by_cases hz : a = 0
    · subst a
      simp [faceCoefficient, he, signedDifference, AddMonoidAlgebra.coeff_add,
        AddMonoidAlgebra.coeff_single, Ne.symm hi, cachedSign_succ]
    · simp [faceCoefficient, he, signedDifference, AddMonoidAlgebra.coeff_add,
        AddMonoidAlgebra.coeff_single, hei, hz]

theorem faceDense_some {row col : Finset (Fin D)} {i : Fin D}
    (he : removedDirection row col = some i) :
    denote (faceDense (-1 : K) row col) =
      constant (cachedSign (-1 : K) (cellPosition col i)) * difference K i := by
  rw [← signedDifference_eq]
  apply denote_eq_of_coeff _ _ (signedDifference_supported i _)
  intro a
  rw [← faceCoefficient_some he]
  simp [faceDense]

theorem faceDense_none {row col : Finset (Fin D)} (he : removedDirection row col = none) :
    denote (faceDense (-1 : K) row col) = 0 := by
  simp [denote, faceDense, faceCoefficient, he]

end
end Decoupling.HighDim.AlgorithmTwoToricData
