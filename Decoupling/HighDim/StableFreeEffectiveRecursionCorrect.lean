import Decoupling.HighDim.StableFreeEffectiveRecursion
import Decoupling.HighDim.StableFreeEffectiveTerminal

/-! Every output of the actual recursion is an actual stable module equivalence. -/
namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic ArithmeticCost
variable {K : Type*} [Field K] {D h₀ length s t : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem powerAdd_zero_right {R : Type*} [CommRing R] {p : ℕ} (x : Power R p) :
    powerAdd p 0 (x,0) = x := by
  funext i
  change powerAdd p 0 (x,0) (finSumFinEquiv (Sum.inl i)) = x i
  rw [powerAdd_apply_sum]
  rfl

private theorem diagonalBlocks_zero_right {R : Type*} [CommRing R] {p : ℕ}
    (E : Matrix (Fin p) (Fin p) R) : diagonalBlocks E (1 : Matrix (Fin 0) (Fin 0) R) = E := by
  apply Matrix.mulVec_injective
  funext x
  have he := diagonalBlocks_mulVec E (1 : Matrix (Fin 0) (Fin 0) R) x 0
  simpa only [Matrix.one_mulVec,powerAdd_zero_right] using he

variable [DecidableEq K]

/-- The computed matrices are mutually inverse on exactly the old projective
summands plus the actual alternating free ranks of the given resolutions. -/
theorem stabilizeProgram_correct (F : DenseTower K D h₀ length s) (G : DenseTower K D h₀ length t)
    {p q h : ℕ} (data : EmbeddedArrays K D s t p q h) (hh : h₀ ≤ h) (hv : StateValid F G data) :
    let out := (stabilizeProgram F G data hh hv).value
    PartialEquiv
      (diagonalBlocks (matrixDenote data.leftProjector)
        (1 : Matrix (Fin (DenseTower.ranks F G).1) (Fin (DenseTower.ranks F G).1) (Laurent K D)))
      (diagonalBlocks (matrixDenote data.rightProjector)
        (1 : Matrix (Fin (DenseTower.ranks F G).2) (Fin (DenseTower.ranks F G).2) (Laurent K D)))
      (matrixDenote out.forward) (matrixDenote out.inverse) := by
  induction F generalizing t p q h with
  | zero =>
      cases G
      simpa only [stabilizeProgram,Work.pure_value,DenseTower.ranks,diagonalBlocks_zero_right] using
        terminal_correct data hv
  | step a A F ih =>
      cases G with
      | step b B G =>
        let solved := solveStage (prepareStage A B data).value (prepareStage_solvable A B F G data hh hv)
        let updated := updateStage data solved.value.1 solved.value.2
        have hnext := updateStage_valid A B F G data hh hv (prepareStage_solvable A B F G data hh hv)
        have hi := ih G updated.value (hh.trans (Nat.le_max_left _ _)) hnext
        have hu := updateStage_correct data solved.value.1 solved.value.2
        dsimp only at hi hu
        rw [hu.1,hu.2.1] at hi
        have hout := hi.symm.reindex (collectOrder p a (DenseTower.ranks F G).2)
          (collectOrder q b (DenseTower.ranks F G).1)
        rw [collectOrder_projector,collectOrder_projector] at hout
        simpa only [stabilizeProgram,Work.bind_value,Work.pure_value,DenseTower.ranks,
          reindexDense_correct,solved,updated] using hout

end Decoupling.HighDim.StableFree.Effective
