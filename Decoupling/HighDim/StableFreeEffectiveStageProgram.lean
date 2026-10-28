import Decoupling.HighDim.StableFreeEffectiveState
import Decoupling.HighDim.StableFreeEffectiveSolve

/-!
# Actual two-solve Schanuel stage

This stage computes the known arrow matrices, calls the complete Laurent
solver twice, and executes both Schanuel block updates. The supplied
solvability propositions are discharged by StateValid in the semantic
interface; no bound or generator certificate is supplied.
-/

namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic ArithmeticCost
variable {K : Type*} [Field K] {D h h₀ s t a b p q : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Fixed block-diagonal coefficient copying. -/
def diagonalBlocksDense {r₁ r₂ c₁ c₂ : ℕ}
    (A : DenseMatrix K D r₁ c₁ h) (B : DenseMatrix K D r₂ c₂ h) :
    DenseMatrix K D (r₁+r₂) (c₁+c₂) h :=
  rowBlocksDense (joinColumns A (zeroMatrixDense K D h r₁ c₂))
    (joinColumns (zeroMatrixDense K D h r₂ c₁) B)

theorem diagonalBlocksDense_correct {r₁ r₂ c₁ c₂ : ℕ}
    (A : DenseMatrix K D r₁ c₁ h) (B : DenseMatrix K D r₂ c₂ h) :
    matrixDenote (diagonalBlocksDense A B) = diagonalBlocks (matrixDenote A) (matrixDenote B) := by
  rw [diagonalBlocksDense,rowBlocksDense_correct,columnBlocksDense_correct,
    columnBlocksDense_correct,zeroMatrixDense_correct,zeroMatrixDense_correct]
  rfl

structure StageArrays (K : Type*) (D v k l h : ℕ) where
  left : DenseMatrix K D v k h
  right : DenseMatrix K D v l h
  sourceLeft : DenseMatrix K D k k h
  sourceRight : DenseMatrix K D l l h

/-- Compute the right arrow by the actual previously computed inverse matrix.
All remaining assembly and padding is pure copying. -/
def prepareStage (A : DenseMatrix K D s a h₀) (B : DenseMatrix K D t b h₀)
    (data : EmbeddedArrays K D s t p q h) :
    Work K (StageArrays K D (s+p) (a+p) (b+q) (h+h)) :=
  Work.bind (matrixMulProgram data.inverse
    (diagonalBlocksDense (matrixPad B h) data.rightProjector)) fun right =>
  Work.pure {
    left := matrixPad (diagonalBlocksDense (matrixPad A h) data.leftProjector) (h+h)
    right := right
    sourceLeft := matrixPad (diagonalBlocksDense (identityDense K D h a) data.leftProjector) (h+h)
    sourceRight := matrixPad (diagonalBlocksDense (identityDense K D h b) data.rightProjector) (h+h) }

@[simp] theorem prepareStage_cost (A : DenseMatrix K D s a h₀) (B : DenseMatrix K D t b h₀)
    (data : EmbeddedArrays K D s t p q h) :
    (prepareStage A B data).cost =
      (s+p)*(b+q)*(t+q)*boxSize D (h+h)*(2*boxSize D h+1) := by
  simp only [prepareStage,Work.bind_cost,matrixMulProgram_cost,Work.pure_cost,add_zero]

theorem prepareStage_correct (A : DenseMatrix K D s a h₀) (B : DenseMatrix K D t b h₀)
    (data : EmbeddedArrays K D s t p q h) (hh : h₀ ≤ h) :
    let out := (prepareStage A B data).value
    matrixDenote out.left = diagonalBlocks (matrixDenote A) (matrixDenote data.leftProjector) ∧
    matrixDenote out.right = matrixDenote data.inverse *
      diagonalBlocks (matrixDenote B) (matrixDenote data.rightProjector) ∧
    matrixDenote out.sourceLeft = diagonalBlocks 1 (matrixDenote data.leftProjector) ∧
    matrixDenote out.sourceRight = diagonalBlocks 1 (matrixDenote data.rightProjector) := by
  dsimp [prepareStage]
  simp only [matrixPad_correct _ (Nat.le_add_right _ _),diagonalBlocksDense_correct,
    matrixPad_correct _ hh,matrixMulProgram_correct,identityDense_correct]
  simp

def StageArrays.Solvable {v k l : ℕ} (data : StageArrays K D v k l h) : Prop :=
  (∃ z : LiftUnknowns k 0 l → Laurent K D,
    liftCoefficients (matrixDenote data.left) 0 (matrixDenote data.sourceLeft)
      (matrixDenote data.sourceRight) *ᵥ z = liftStack (matrixDenote data.right) 0 0) ∧
  (∃ z : LiftUnknowns l 0 k → Laurent K D,
    liftCoefficients (matrixDenote data.right) 0 (matrixDenote data.sourceRight)
      (matrixDenote data.sourceLeft) *ᵥ z = liftStack (matrixDenote data.left) 0 0)

def stageLiftBox (D v k l h : ℕ) : ℕ :=
  max (LaurentLinearSolver.outputBox D ((v+(k+k))*l) h)
    (LaurentLinearSolver.outputBox D ((v+(l+l))*k) h)

def nextStageBox (D s a b p q h : ℕ) : ℕ :=
  max h (stageLiftBox D (s+p) (a+p) (b+q) (h+h) +
    stageLiftBox D (s+p) (a+p) (b+q) (h+h))

variable [DecidableEq K]

def solveStage {v k l : ℕ} (data : StageArrays K D v k l h) (hs : data.Solvable) :
    Work K (DenseMatrix K D k l (stageLiftBox D v k l h) ×
      DenseMatrix K D l k (stageLiftBox D v k l h)) :=
  let leftSol := solveLiftProgram data.left data.right (zeroMatrixDense K D h v 0)
    data.sourceLeft data.sourceRight (by simpa only [zeroMatrixDense_correct] using hs.1)
  let rightSol := solveLiftProgram data.right data.left (zeroMatrixDense K D h v 0)
    data.sourceRight data.sourceLeft (by simpa only [zeroMatrixDense_correct] using hs.2)
  Work.bind leftSol fun x => Work.bind rightSol fun y =>
    Work.pure (matrixPad x.1 (stageLiftBox D v k l h),matrixPad y.1 (stageLiftBox D v k l h))

theorem solveStage_correct {v k l : ℕ} (data : StageArrays K D v k l h) (hs : data.Solvable) :
    let out := (solveStage data hs).value
    matrixDenote data.left * matrixDenote out.1 = matrixDenote data.right ∧
    matrixDenote data.sourceLeft * matrixDenote out.1 = matrixDenote out.1 ∧
    matrixDenote out.1 * matrixDenote data.sourceRight = matrixDenote out.1 ∧
    matrixDenote data.right * matrixDenote out.2 = matrixDenote data.left ∧
    matrixDenote data.sourceRight * matrixDenote out.2 = matrixDenote out.2 ∧
    matrixDenote out.2 * matrixDenote data.sourceLeft = matrixDenote out.2 := by
  have hU := solveLiftProgram_correct data.left data.right (zeroMatrixDense K D h v 0)
    data.sourceLeft data.sourceRight (by simpa only [zeroMatrixDense_correct] using hs.1)
  have hV := solveLiftProgram_correct data.right data.left (zeroMatrixDense K D h v 0)
    data.sourceRight data.sourceLeft (by simpa only [zeroMatrixDense_correct] using hs.2)
  dsimp [solveStage]
  unfold stageLiftBox
  rw [matrixPad_correct _ (Nat.le_max_left _ _),matrixPad_correct _ (Nat.le_max_right _ _)]
  simp only [zeroMatrixDense_correct,Matrix.zero_mul,sub_eq_zero] at hU hV
  exact ⟨hU.1,hU.2.1,hU.2.2,hV.1,hV.2.1,hV.2.2⟩

theorem solveStage_cost {v k l : ℕ} (data : StageArrays K D v k l h) (hs : data.Solvable) :
    (solveStage data hs).cost ≤ liftSolveCost D v 0 k l h+liftSolveCost D v 0 l k h := by
  unfold solveStage
  simp only [Work.bind_cost,Work.pure_cost,add_zero]
  exact Nat.add_le_add (solveLiftProgram_cost _ _ _ _ _ _) (solveLiftProgram_cost _ _ _ _ _ _)

/-- Execute both computed updates, with common output padding that retains
all input differential boxes even in zero-row or zero-column cases. -/
def updateStage (data : EmbeddedArrays K D s t p q h)
    (U : DenseMatrix K D (a+p) (b+q) (stageLiftBox D (s+p) (a+p) (b+q) (h+h)))
    (V : DenseMatrix K D (b+q) (a+p) (stageLiftBox D (s+p) (a+p) (b+q) (h+h))) :
    Work K (EmbeddedArrays K D a b (b+q) (a+p) (nextStageBox D s a b p q h)) :=
  Work.bind (stepForwardProgram U V) fun forward =>
    Work.bind (stepInverseProgram U V) fun inverse => Work.pure {
      leftProjector := matrixPad (diagonalBlocksDense (identityDense K D h b) data.rightProjector) _
      rightProjector := matrixPad (diagonalBlocksDense (identityDense K D h a) data.leftProjector) _
      forward := matrixPad forward _
      inverse := matrixPad inverse _ }

omit [DecidableEq K] in
theorem updateStage_correct (data : EmbeddedArrays K D s t p q h)
    (U : DenseMatrix K D (a+p) (b+q) (stageLiftBox D (s+p) (a+p) (b+q) (h+h)))
    (V : DenseMatrix K D (b+q) (a+p) (stageLiftBox D (s+p) (a+p) (b+q) (h+h))) :
    let out := (updateStage data U V).value
    matrixDenote out.leftProjector = diagonalBlocks 1 (matrixDenote data.rightProjector) ∧
    matrixDenote out.rightProjector = diagonalBlocks 1 (matrixDenote data.leftProjector) ∧
    matrixDenote out.forward = stepForward a b p q (matrixDenote U) (matrixDenote V) ∧
    matrixDenote out.inverse = stepInverse a b p q (matrixDenote U) (matrixDenote V) := by
  dsimp [updateStage]
  unfold nextStageBox
  simp only [matrixPad_correct _ (Nat.le_max_left _ _),
    matrixPad_correct _ (Nat.le_max_right _ _),diagonalBlocksDense_correct,
    identityDense_correct,stepForwardProgram_correct,stepInverseProgram_correct]
  simp

end Decoupling.HighDim.StableFree.Effective
