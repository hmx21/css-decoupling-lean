import Decoupling.HighDim.StableFreeEffectiveTower
import Decoupling.HighDim.StableFreeSequence

/-! Actual stored differential slices model the actual successive kernel covers. -/
namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic CategoryTheory.Limits
universe u
variable {K : Type u} [Field K] {D h : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace DenseTower

/-- Pure runtime tower made from the specified consecutive input matrices. -/
def ofDifferentials (rank : ℕ → ℕ)
    (matrices : ∀ i, DenseMatrix K D (rank i) (rank (i+1)) h) :
    (length : ℕ) → DenseTower K D h length (rank 0)
  | 0 => .zero _
  | n+1 => .step (rank 1) (matrices 0)
      (ofDifferentials (fun i => rank (i+1)) (fun i => matrices (i+1)) n)

/-- Applied to checkSequence, these are precisely the actual negative-degree
free differential slices. The only inputs besides the arrays are their
literal coordinate equalities and the already proved finite support. -/
theorem ofDifferentials_models_tail {M : ModuleCat.{u} (Laurent K D)}
    (A : Sequence M) (matrices : ∀ i, DenseMatrix K D (A.rank i) (A.rank (i+1)) h)
    (hm : ∀ i, matrixDenote (matrices i) = LinearMap.toMatrix'
      ((A.coordinates i).toLinearMap.comp ((A.d i).comp (A.coordinates (i+1)).symm.toLinearMap)))
    (length : ℕ) (hz : ∀ i, length+1 ≤ i → IsZero (A.X i)) :
    Models (ofDifferentials A.rank matrices length)
      (ModuleCat.of (Laurent K D) (LinearMap.ker A.ε))
      ((A.coordinates 0).toLinearMap.comp (LinearMap.ker A.ε).subtype) := by
  induction length generalizing M with
  | zero =>
      apply Models.zero
      intro x
      obtain ⟨y,rfl⟩ := A.tailMap_surjective x
      have hy : y = 0 := (ModuleCat.subsingleton_of_isZero (hz 1 (by omega))).elim _ _
      rw [hy,map_zero]
  | succ length ih =>
      refine Models.step (A.X 1) (A.coordinates 1) A.tailMap A.tailMap_surjective ?_ ?_
      · rw [hm 0]
        congr 1
      · exact ih A.tail (fun i => matrices (i+1)) (fun i => hm (i+1))
          (fun i hi => hz (i+1) (by omega))

end DenseTower
end Decoupling.HighDim.StableFree.Effective
