import Decoupling.HighDim.StableFreeEffectiveInitialProgram

/-!
# HD012 the initial dense program computes the actual presented arrows

`Realizes` only identifies stored input coefficients with the known
coordinate matrices of the actual homotopy data. It does not assume a
stable isomorphism, a complement basis, a lifting solution or a cost.
-/
namespace Decoupling.HighDim.StableFree.Effective.Initial
open Matrix ArithmeticCost LaurentArithmetic CategoryTheory
variable {K : Type*} [Field K] {D c n p e rel h : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace Inputs
variable (i : Inputs K D c n p e rel h)

theorem makeL_correct :
    matrixDenote i.makeL.value =
      joinCols (matrixDenote i.T) (-(matrixDenote i.F * matrixDenote i.Z)) := by
  simp only [makeL, Work.bind_value, Work.pure_value]
  rw [cols_correct, matrixPad_correct _ (by dsimp [radius2]; omega),
    matrixNegProgram_correct, matrixMulProgram_correct]

theorem makeR_correct (L : DenseMatrix K D n (e+p) (radius2 h)) :
    matrixDenote (i.makeR L).value =
      matrixDenote i.G * matrixDenote L + joinCols 0 (matrixDenote i.Z) := by
  simp only [makeR, Work.bind_value]
  rw [addSame_correct, matrixMulProgram_correct,
    matrixPad_correct _ (by dsimp [radius3,radius2]; omega), cols_correct, zeroMatrix_correct]

theorem makeQN_correct (L : DenseMatrix K D n (e+p) (radius2 h))
    (R : DenseMatrix K D c (e+p) (radius3 h)) :
    matrixDenote (i.makeQN L R).value = matrixDenote L - matrixDenote i.F * matrixDenote R := by
  simp only [makeQN, Work.bind_value]
  rw [subSame_correct, matrixMulProgram_correct,
    matrixPad_correct _ (by dsimp [radius4,radius3,radius2]; omega)]

theorem makeQP_correct (R : DenseMatrix K D c (e+p) (radius3 h)) :
    matrixDenote (i.makeQP R).value =
      joinCols 0 (1 : Matrix (Fin p) (Fin p) (Laurent K D)) -
        matrixDenote i.X * matrixDenote R := by
  simp only [makeQP, Work.bind_value]
  rw [subSame_correct, cols_correct, zeroMatrix_correct, identityDense_correct,
    matrixMulProgram_correct]

theorem makeQ_correct (QN : DenseMatrix K D n (e+p) (radius4 h))
    (QP : DenseMatrix K D p (e+p) (radius4 h)) :
    matrixDenote (i.makeQ QN QP).value =
      joinRows (matrixDenote i.Y * matrixDenote QN) (matrixDenote QP) := by
  simp only [makeQ, Work.bind_value, Work.pure_value]
  rw [rows_correct, matrixMulProgram_correct,
    matrixPad_correct _ (by dsimp [radius5,radius4,radius3,radius2]; omega)]

end Inputs

variable {M N : ModuleCat (Laurent K D)}

structure Realizes (i : Inputs K D c n p e rel h) (a : Data M N c n p e rel) : Prop where
  F : matrixDenote i.F = a.matrixF
  G : matrixDenote i.G = a.matrixG
  X : matrixDenote i.X = a.matrixX
  Y : matrixDenote i.Y = a.matrixY
  Z : matrixDenote i.Z = a.matrixZ
  T : matrixDenote i.T = a.matrixT
  relations : matrixDenote i.relations = a.relations

/-- Every stored output is the actual matrix required by the first
Schanuel step. In particular, the two projectors represent the genuine
projective modules and the relation matrix presents the actual target. -/
theorem run_correct (i : Inputs K D c n p e rel h) (a : Data M N c n p e rel)
    (hi : Realizes i a) :
    matrixDenote i.run.value.alpha = a.alphaArrow.matrix ∧
    matrixDenote i.run.value.beta = a.betaArrow.matrix ∧
    matrixDenote i.run.value.relations = a.target.relationMatrix ∧
    matrixDenote i.run.value.leftProjector = a.sourceLeft.projector ∧
    matrixDenote i.run.value.rightProjector = a.sourceRight.projector ∧
    matrixDenote i.run.value.complementProjector = a.complement.projector := by
  let L := i.makeL.value
  let R := (i.makeR L).value
  let QN := (i.makeQN L R).value
  let QP := (i.makeQP R).value
  let Q := (i.makeQ QN QP).value
  have hL : matrixDenote L = a.matrixL := by
    rw [i.makeL_correct, hi.T, hi.F, hi.Z]
    rfl
  have hR : matrixDenote R = a.matrixR := by
    rw [i.makeR_correct L, hi.G, hL, hi.Z]
    rfl
  have hQN : matrixDenote QN = a.matrixQN := by
    rw [i.makeQN_correct L R, hL, hi.F, hR]
    rfl
  have hQP : matrixDenote QP = a.matrixQP := by
    rw [i.makeQP_correct R, hi.X, hR]
    rfl
  have hQ : matrixDenote Q = a.matrixQ := by
    rw [i.makeQ_correct QN QP, hi.Y, hQN, hQP]
    rfl
  change matrixDenote (i.makeOutput QN QP Q).alpha = _ ∧
    matrixDenote (i.makeOutput QN QP Q).beta = _ ∧
    matrixDenote (i.makeOutput QN QP Q).relations = _ ∧
    matrixDenote (i.makeOutput QN QP Q).leftProjector = _ ∧
    matrixDenote (i.makeOutput QN QP Q).rightProjector = _ ∧
    matrixDenote (i.makeOutput QN QP Q).complementProjector = _
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · exact identityDense_correct.trans a.alphaArrow_matrix.symm
  · change matrixDenote (matrixPad _ (radius5 h)) = _
    rw [matrixPad_correct _ (by dsimp [radius5]; omega), rows_correct, cols_correct, cols_correct,
      matrixPad_correct _ (by dsimp [radius4,radius3,radius2]; omega),
      matrixPad_correct _ (by dsimp [radius4,radius3,radius2]; omega),
      hi.F, hi.X, hQN, hQP, a.betaArrow_matrix]
    rfl
  · change matrixDenote (matrixPad _ (radius5 h)) = _
    rw [matrixPad_correct _ (by dsimp [radius5,radius4,radius3,radius2]; omega),
      rows_correct, zeroMatrix_correct, hi.relations, a.target_relations]
    rfl
  · exact identityDense_correct.trans a.sourceLeft_projector.symm
  · change matrixDenote (rows _ _) = _
    rw [rows_correct, cols_correct, cols_correct, identityDense_correct,
      zeroMatrix_correct, zeroMatrix_correct, hQ, a.sourceRight_projector]
    rfl
  · exact hQ.trans a.complement_projector.symm

end Decoupling.HighDim.StableFree.Effective.Initial
