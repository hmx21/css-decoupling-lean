import Decoupling.HighDim.StableFreeEffectiveBeta
import Decoupling.HighDim.StableFreeEffectiveDimensions

/-!
# Actual stable check-cokernel program from the initial presentation and resolutions

The stable-complement matrices are computed by the full recursion, then
absorbed into the two known initial presentation lifts. In particular no
stable-complement matrix or stable-check map is an input to this program.
The initial solvability and state interpretation are derived by
firstStage_solvable / firstStage_valid from the actual native initial maps.
-/
namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic ArithmeticCost
universe u
variable {K : Type u} [Field K] [DecidableEq K]
  {D h h₀ length v rel a b p q n m : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def stableCheckProgram
    (data : PresentedStageArrays K D v (a+p) (b+q) rel h)
    (EQ : DenseMatrix K D q q h)
    (L : DenseMatrix K D (m+q) (n+p) h) (Linv : DenseMatrix K D (n+p) (m+q) h)
    (F : DenseTower K D h₀ length a) (G : DenseTower K D h₀ length b)
    (hh : h₀ ≤ h) (hs : data.Solvable)
    (hv : StateValid F G (firstUpdate (identityDense K D h p) EQ
      (solvePresentedStage data hs).value.1 (solvePresentedStage data hs).value.2.1).value) :=
  Work.bind (fullStabilizeProgram data (identityDense K D h p) EQ F G hh hs hv) fun stable =>
    absorbProgram L Linv stable.forward stable.inverse EQ

/-- Real stable-check beta and its two returned presentation matrices. The
stable-complement inverse identities are proved internally by the recursion. -/
theorem stableCheckProgram_presents {M N Q : ModuleCat.{u} (Laurent K D)}
    (πN : Power (Laurent K D) n →ₗ[Laurent K D] N)
    (πM : Power (Laurent K D) m →ₗ[Laurent K D] M)
    (rq : RetractAt Q q) (e : (N × Power (Laurent K D) p) ≃ₗ[Laurent K D] (M × Q))
    (data : PresentedStageArrays K D v (a+p) (b+q) rel h)
    (EQ : DenseMatrix K D q q h) (hEQ : matrixDenote EQ = rq.model.projector)
    (L : DenseMatrix K D (m+q) (n+p) h) (Linv : DenseMatrix K D (n+p) (m+q) h)
    (hL : ∀ x, (πM.prodMap rq.project)
      ((powerAdd m q).symm (matrixDenote L *ᵥ x)) = e (stabilizedQuotient πN p x))
    (hLinv : ∀ x, stabilizedQuotient πN p (matrixDenote Linv *ᵥ x) =
      e.symm ((πM.prodMap rq.project) ((powerAdd m q).symm x)))
    (F : DenseTower K D h₀ length a) (G : DenseTower K D h₀ length b)
    (hh : h₀ ≤ h) (hs : data.Solvable)
    (hv : StateValid F G (firstUpdate (identityDense K D h p) EQ
      (solvePresentedStage data hs).value.1 (solvePresentedStage data hs).value.2.1).value) :
    ∃ beta : (N × Power (Laurent K D) (p+(b+(F.ranks G).1))) ≃ₗ[Laurent K D]
        (M × Power (Laurent K D) (p+(a+(F.ranks G).2))),
      (∀ x, stabilizedQuotient πM _
        (matrixDenote (stableCheckProgram data EQ L Linv F G hh hs hv).value.forward *ᵥ x) =
          beta (stabilizedQuotient πN _ x)) ∧
      (∀ x, stabilizedQuotient πN _
        (matrixDenote (stableCheckProgram data EQ L Linv F G hh hs hv).value.inverse *ᵥ x) =
          beta.symm (stabilizedQuotient πM _ x)) := by
  have hp := fullStabilizeProgram_correct data (identityDense K D h p) EQ F G hh hs hv
  rw [identityDense_correct,diagonalBlocks_one_one] at hp
  exact absorbProgram_presents πN πM rq e L Linv _ _ EQ hEQ hp hL hLinv

/-- Bound for the complete calculated stabilization and beta absorption. -/
theorem stableCheckProgram_cost
    (data : PresentedStageArrays K D v (a+p) (b+q) rel h)
    (EQ : DenseMatrix K D q q h)
    (L : DenseMatrix K D (m+q) (n+p) h) (Linv : DenseMatrix K D (n+p) (m+q) h)
    (F : DenseTower K D h₀ length a) (G : DenseTower K D h₀ length b)
    (hh : h₀ ≤ h) (hs : data.Solvable)
    (hv : StateValid F G (firstUpdate (identityDense K D h p) EQ
      (solvePresentedStage data hs).value.1 (solvePresentedStage data hs).value.2.1).value) :
    let next := max h (stageLiftBox D v (a+p) (b+q) h+stageLiftBox D v (a+p) (b+q) h)
    (stableCheckProgram data EQ L Linv F G hh hs hv).cost ≤
      ((liftSolveCost D v rel (a+p) (b+q) h+liftSolveCost D v rel (b+q) (a+p) h) +
      DenseTower.updateCost D a b p q (stageLiftBox D v (a+p) (b+q) h) +
      F.costBound G (b+q) (a+p) next) +
      absorbCost D n m p q (a+(F.ranks G).2) (b+(F.ranks G).1) h
        (F.outputBox G (b+q) (a+p) next) h := by
  dsimp only
  rw [stableCheckProgram,Work.bind_cost,absorbProgram_cost]
  exact Nat.add_le_add_right (fullStabilizeProgram_cost data (identityDense K D h p) EQ F G hh hs hv) _

end Decoupling.HighDim.StableFree.Effective
