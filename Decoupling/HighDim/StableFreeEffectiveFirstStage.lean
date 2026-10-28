import Decoupling.HighDim.StableFreeEffectiveStageCorrect

/-!
# The actual first quotient stage

Unlike later embedded syzygies, the initial common target can have nonzero
relations. This program uses the supplied actual presentation matrices and
the same complete Laurent solver, then returns the first embedded state.
Its module hypotheses are just the actual initial equivalence and covers.
-/

namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic ArithmeticCost
variable {K : Type*} [Field K] {D h v k l rel a b p q : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

structure PresentedStageArrays (K : Type*) (D v k l rel h : ℕ) where
  left : DenseMatrix K D v k h
  right : DenseMatrix K D v l h
  relations : DenseMatrix K D v rel h
  sourceLeft : DenseMatrix K D k k h
  sourceRight : DenseMatrix K D l l h

def PresentedStageArrays.Solvable (data : PresentedStageArrays K D v k l rel h) : Prop :=
  (∃ z : LiftUnknowns k rel l → Laurent K D,
    liftCoefficients (matrixDenote data.left) (matrixDenote data.relations)
      (matrixDenote data.sourceLeft) (matrixDenote data.sourceRight) *ᵥ z =
      liftStack (matrixDenote data.right) 0 0) ∧
  (∃ z : LiftUnknowns l rel k → Laurent K D,
    liftCoefficients (matrixDenote data.right) (matrixDenote data.relations)
      (matrixDenote data.sourceRight) (matrixDenote data.sourceLeft) *ᵥ z =
      liftStack (matrixDenote data.left) 0 0)

variable [DecidableEq K]

/-- The relation witnesses are retained in the actual solver output, even
though the Schanuel block update only needs the two normalized lifts. -/
def solvePresentedStage (data : PresentedStageArrays K D v k l rel h) (hs : data.Solvable) :
    Work K (DenseMatrix K D k l (stageLiftBox D v k l h) ×
      DenseMatrix K D l k (stageLiftBox D v k l h) ×
      DenseMatrix K D rel l (stageLiftBox D v k l h) ×
      DenseMatrix K D rel k (stageLiftBox D v k l h)) :=
  let leftSol := solveLiftProgram data.left data.right data.relations data.sourceLeft data.sourceRight hs.1
  let rightSol := solveLiftProgram data.right data.left data.relations data.sourceRight data.sourceLeft hs.2
  Work.bind leftSol fun x => Work.bind rightSol fun y =>
    Work.pure (matrixPad x.1 _,matrixPad y.1 _,matrixPad x.2 _,matrixPad y.2 _)

theorem solvePresentedStage_correct (data : PresentedStageArrays K D v k l rel h) (hs : data.Solvable) :
    let out := (solvePresentedStage data hs).value
    matrixDenote data.left * matrixDenote out.1 - matrixDenote data.right =
      matrixDenote data.relations * matrixDenote out.2.2.1 ∧
    matrixDenote data.sourceLeft * matrixDenote out.1 = matrixDenote out.1 ∧
    matrixDenote out.1 * matrixDenote data.sourceRight = matrixDenote out.1 ∧
    matrixDenote data.right * matrixDenote out.2.1 - matrixDenote data.left =
      matrixDenote data.relations * matrixDenote out.2.2.2 ∧
    matrixDenote data.sourceRight * matrixDenote out.2.1 = matrixDenote out.2.1 ∧
    matrixDenote out.2.1 * matrixDenote data.sourceLeft = matrixDenote out.2.1 := by
  have hU := solveLiftProgram_correct data.left data.right data.relations data.sourceLeft data.sourceRight hs.1
  have hV := solveLiftProgram_correct data.right data.left data.relations data.sourceRight data.sourceLeft hs.2
  dsimp [solvePresentedStage]
  unfold stageLiftBox
  rw [matrixPad_correct _ (Nat.le_max_left _ _),matrixPad_correct _ (Nat.le_max_left _ _),
    matrixPad_correct _ (Nat.le_max_right _ _),matrixPad_correct _ (Nat.le_max_right _ _)]
  exact ⟨hU.1,hU.2.1,hU.2.2,hV.1,hV.2.1,hV.2.2⟩

theorem solvePresentedStage_cost (data : PresentedStageArrays K D v k l rel h) (hs : data.Solvable) :
    (solvePresentedStage data hs).cost ≤ liftSolveCost D v rel k l h+liftSolveCost D v rel l k h := by
  unfold solvePresentedStage
  simp only [Work.bind_cost,Work.pure_cost,add_zero]
  exact Nat.add_le_add (solveLiftProgram_cost _ _ _ _ _ _) (solveLiftProgram_cost _ _ _ _ _ _)

variable {H : ℕ}
/-- Execute the first represented update with the original factor projectors. -/
def firstUpdate (EP : DenseMatrix K D p p h) (EQ : DenseMatrix K D q q h)
    (U : DenseMatrix K D (a+p) (b+q) H) (V : DenseMatrix K D (b+q) (a+p) H) :
    Work K (EmbeddedArrays K D a b (b+q) (a+p) (max h (H+H))) :=
  Work.bind (stepForwardProgram U V) fun forward =>
    Work.bind (stepInverseProgram U V) fun inverse => Work.pure {
      leftProjector := matrixPad (diagonalBlocksDense (identityDense K D h b) EQ) _
      rightProjector := matrixPad (diagonalBlocksDense (identityDense K D h a) EP) _
      forward := matrixPad forward _
      inverse := matrixPad inverse _ }

omit [DecidableEq K] in
theorem firstUpdate_correct (EP : DenseMatrix K D p p h) (EQ : DenseMatrix K D q q h)
    (U : DenseMatrix K D (a+p) (b+q) H) (V : DenseMatrix K D (b+q) (a+p) H) :
    let out := (firstUpdate EP EQ U V).value
    matrixDenote out.leftProjector = diagonalBlocks 1 (matrixDenote EQ) ∧
    matrixDenote out.rightProjector = diagonalBlocks 1 (matrixDenote EP) ∧
    matrixDenote out.forward = stepForward a b p q (matrixDenote U) (matrixDenote V) ∧
    matrixDenote out.inverse = stepInverse a b p q (matrixDenote U) (matrixDenote V) := by
  dsimp [firstUpdate]
  simp only [matrixPad_correct _ (Nat.le_max_left _ _),matrixPad_correct _ (Nat.le_max_right _ _),
    diagonalBlocksDense_correct,identityDense_correct,stepForwardProgram_correct,stepInverseProgram_correct]
  simp

end Decoupling.HighDim.StableFree.Effective
