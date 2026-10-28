import Decoupling.HighDim.StableFreeEffectiveFirstCorrect
import Decoupling.HighDim.StableFreeEffectiveRecursionCorrect

/-!
# Initial quotient lifting followed by the entire actual Schanuel recursion

Only the genuine initial presentation, stored projectors and original finite
resolution arrays enter. Every output is calculated by the explicit solver,
block arithmetic and field-independent permutations. Correctness is supplied
by the actual semantic initial state, not a requested-output certificate.
-/
namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic ArithmeticCost
variable {K : Type*} [Field K] [DecidableEq K] {D h h₀ length v rel a b p q : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Full initial stage and recursion, retaining the original two factor
orders and their explicitly calculated alternating free ranks. -/
def fullStabilizeProgram
    (data : PresentedStageArrays K D v (a+p) (b+q) rel h)
    (EP : DenseMatrix K D p p h) (EQ : DenseMatrix K D q q h)
    (F : DenseTower K D h₀ length a) (G : DenseTower K D h₀ length b)
    (hh : h₀ ≤ h) (hs : data.Solvable)
    (hv : StateValid F G (firstUpdate EP EQ (solvePresentedStage data hs).value.1
      (solvePresentedStage data hs).value.2.1).value) :
    Work K (StableArrays K D p q (a+(F.ranks G).2) (b+(F.ranks G).1)
      (F.outputBox G (b+q) (a+p)
        (max h (stageLiftBox D v (a+p) (b+q) h+stageLiftBox D v (a+p) (b+q) h)))) :=
  let solved := solvePresentedStage data hs
  let updated := firstUpdate EP EQ solved.value.1 solved.value.2.1
  let recursive := stabilizeProgram F G updated.value (hh.trans (Nat.le_max_left _ _)) hv
  Work.bind solved fun _ => Work.bind updated fun _ => Work.bind recursive fun out =>
    Work.pure {
      forward := reindexDense out.inverse (collectOrder q b (F.ranks G).1) (collectOrder p a (F.ranks G).2)
      inverse := reindexDense out.forward (collectOrder p a (F.ranks G).2) (collectOrder q b (F.ranks G).1)
      solverSystems := ((v+((a+p)+(a+p)))*(b+q),((a+p)+rel)*(b+q),h) ::
        ((v+((b+q)+(b+q)))*(a+p),((b+q)+rel)*(a+p),h) :: out.solverSystems }

/-- The full computed stabilization is inverse on the actual enlarged
projector images, with no free-complement premise. -/
theorem fullStabilizeProgram_correct
    (data : PresentedStageArrays K D v (a+p) (b+q) rel h)
    (EP : DenseMatrix K D p p h) (EQ : DenseMatrix K D q q h)
    (F : DenseTower K D h₀ length a) (G : DenseTower K D h₀ length b)
    (hh : h₀ ≤ h) (hs : data.Solvable)
    (hv : StateValid F G (firstUpdate EP EQ (solvePresentedStage data hs).value.1
      (solvePresentedStage data hs).value.2.1).value) :
    let out := (fullStabilizeProgram data EP EQ F G hh hs hv).value
    PartialEquiv (diagonalBlocks (matrixDenote EP) (1 : Matrix (Fin (a+(F.ranks G).2)) _ _))
      (diagonalBlocks (matrixDenote EQ) (1 : Matrix (Fin (b+(F.ranks G).1)) _ _))
      (matrixDenote out.forward) (matrixDenote out.inverse) := by
  let solved := solvePresentedStage data hs
  let updated := firstUpdate EP EQ solved.value.1 solved.value.2.1
  have hi := stabilizeProgram_correct F G updated.value (hh.trans (Nat.le_max_left _ _)) hv
  have hu := firstUpdate_correct EP EQ solved.value.1 solved.value.2.1
  dsimp only at hi hu
  rw [hu.1,hu.2.1] at hi
  have ho := hi.symm.reindex (collectOrder p a (F.ranks G).2) (collectOrder q b (F.ranks G).1)
  rw [collectOrder_projector,collectOrder_projector] at ho
  simpa only [fullStabilizeProgram,Work.bind_value,Work.pure_value,reindexDense_correct,solved,updated] using ho

omit [DecidableEq K] in
theorem firstUpdate_cost {H : ℕ} (EP : DenseMatrix K D p p h) (EQ : DenseMatrix K D q q h)
    (U : DenseMatrix K D (a+p) (b+q) H) (V : DenseMatrix K D (b+q) (a+p) H) :
    (firstUpdate EP EQ U V).cost = DenseTower.updateCost D a b p q H := by
  simp only [firstUpdate,Work.bind_cost,Work.pure_cost,add_zero,
    stepForwardProgram_cost,stepInverseProgram_cost,DenseTower.updateCost]

theorem fullStabilizeProgram_cost
    (data : PresentedStageArrays K D v (a+p) (b+q) rel h)
    (EP : DenseMatrix K D p p h) (EQ : DenseMatrix K D q q h)
    (F : DenseTower K D h₀ length a) (G : DenseTower K D h₀ length b)
    (hh : h₀ ≤ h) (hs : data.Solvable)
    (hv : StateValid F G (firstUpdate EP EQ (solvePresentedStage data hs).value.1
      (solvePresentedStage data hs).value.2.1).value) :
    (fullStabilizeProgram data EP EQ F G hh hs hv).cost ≤
      (liftSolveCost D v rel (a+p) (b+q) h+liftSolveCost D v rel (b+q) (a+p) h) +
      DenseTower.updateCost D a b p q (stageLiftBox D v (a+p) (b+q) h) +
      F.costBound G (b+q) (a+p)
        (max h (stageLiftBox D v (a+p) (b+q) h+stageLiftBox D v (a+p) (b+q) h)) := by
  simp only [fullStabilizeProgram,Work.bind_cost,Work.pure_cost,add_zero,firstUpdate_cost]
  have hs' := solvePresentedStage_cost data hs
  have hr := stabilizeProgram_cost F G
    (firstUpdate EP EQ (solvePresentedStage data hs).value.1 (solvePresentedStage data hs).value.2.1).value
    (hh.trans (Nat.le_max_left _ _)) hv
  omega


/-- Initial quotient stage plus the exact number of actual recursive levels. -/
theorem fullStabilizeProgram_solver_count
    (data : PresentedStageArrays K D v (a+p) (b+q) rel h)
    (EP : DenseMatrix K D p p h) (EQ : DenseMatrix K D q q h)
    (F : DenseTower K D h₀ length a) (G : DenseTower K D h₀ length b)
    (hh : h₀ ≤ h) (hs : data.Solvable)
    (hv : StateValid F G (firstUpdate EP EQ (solvePresentedStage data hs).value.1
      (solvePresentedStage data hs).value.2.1).value) :
    (fullStabilizeProgram data EP EQ F G hh hs hv).value.solverSystems.length = 2*(length+1) := by
  simp only [fullStabilizeProgram,Work.bind_value,Work.pure_value,List.length_cons,
    stabilizeProgram_solver_count]
  omega

end Decoupling.HighDim.StableFree.Effective
