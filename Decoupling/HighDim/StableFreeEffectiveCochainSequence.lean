import Decoupling.HighDim.StableFreeEffectiveTowerSequence
import Decoupling.HighDim.StableFreeCochain

/-!
# Actual check resolutions in their supplied free coordinates

This changes only the already supplied finite free terms. The quotient is
unchanged, and its successive kernels are the literal kernels of the
coordinate augmentation used by Initial.homotopyData.
-/
namespace Decoupling.HighDim.StableFree.Effective.CochainProgram
open Matrix CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
variable {R : Type u} [CommRing R] {M : ModuleCat.{u} R}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Recoordinate every supplied free term, without changing the augmented
module and without choosing any new basis. -/
def coordinateSequence (A : Sequence M) : Sequence M where
  X i := ModuleCat.of R (Power R (A.rank i))
  rank := A.rank
  coordinates _ := LinearEquiv.refl R _
  d i := (A.coordinates i).toLinearMap.comp ((A.d i).comp (A.coordinates (i+1)).symm.toLinearMap)
  ε := A.ε.comp (A.coordinates 0).symm.toLinearMap
  surjective := A.surjective.comp (A.coordinates 0).symm.surjective
  exact_zero := by
    ext x
    change (∃ y, A.coordinates 0 (A.d 0 ((A.coordinates 1).symm y)) = x) ↔
      A.ε ((A.coordinates 0).symm x) = 0
    constructor
    · rintro ⟨y,hy⟩
      have hx : (A.coordinates 0).symm x ∈ LinearMap.range (A.d 0) :=
        ⟨(A.coordinates 1).symm y,(A.coordinates 0).injective (hy.trans ((A.coordinates 0).apply_symm_apply x).symm)⟩
      rw [A.exact_zero] at hx
      exact hx
    · intro hx
      have hx' : (A.coordinates 0).symm x ∈ LinearMap.range (A.d 0) := by
        rw [A.exact_zero]; exact hx
      obtain ⟨y,hy⟩ := hx'
      refine ⟨A.coordinates 1 y,?_⟩
      rw [LinearEquiv.symm_apply_apply,hy,LinearEquiv.apply_symm_apply]
  exact_succ i := by
    ext x
    change (∃ y, A.coordinates (i+1) (A.d (i+1) ((A.coordinates (i+1+1)).symm y)) = x) ↔
      A.coordinates i (A.d i ((A.coordinates (i+1)).symm x)) = 0
    rw [map_eq_zero_iff _ (A.coordinates i).injective]
    constructor
    · rintro ⟨y,hy⟩
      have hx : (A.coordinates (i+1)).symm x ∈ LinearMap.range (A.d (i+1)) :=
        ⟨(A.coordinates (i+1+1)).symm y,
          (A.coordinates (i+1)).injective (hy.trans ((A.coordinates (i+1)).apply_symm_apply x).symm)⟩
      rw [A.exact_succ] at hx
      exact hx
    · intro hx
      have hx' : (A.coordinates (i+1)).symm x ∈ LinearMap.range (A.d (i+1)) := by
        rw [A.exact_succ]; exact hx
      obtain ⟨y,hy⟩ := hx'
      refine ⟨A.coordinates (i+1+1) y,?_⟩
      rw [LinearEquiv.symm_apply_apply,hy,LinearEquiv.apply_symm_apply]

variable {K : Type u} [Field K] {D h : ℕ}

/-- The stored original differential arrays model the literal coordinate
augmentation kernel used by the executable initial stage. -/
theorem coordinateSequence_models {M : ModuleCat.{u} (Laurent K D)}
    (A : Sequence M) (matrices : ∀ i, LaurentArithmetic.DenseMatrix K D (A.rank i) (A.rank (i+1)) h)
    (hm : ∀ i, LaurentArithmetic.matrixDenote (matrices i) = LinearMap.toMatrix'
      ((A.coordinates i).toLinearMap.comp ((A.d i).comp (A.coordinates (i+1)).symm.toLinearMap)))
    (length : ℕ) (hz : ∀ i, length+1 ≤ i → IsZero (A.X i)) :
    DenseTower.Models (DenseTower.ofDifferentials A.rank matrices length)
      (ModuleCat.of (Laurent K D) (LinearMap.ker (A.ε.comp (A.coordinates 0).symm.toLinearMap)))
      (LinearMap.ker (A.ε.comp (A.coordinates 0).symm.toLinearMap)).subtype := by
  apply DenseTower.ofDifferentials_models_tail (coordinateSequence A) matrices
  · intro i
    simpa [coordinateSequence] using hm i
  · intro i hi
    let : Subsingleton (A.X i) := ModuleCat.subsingleton_of_isZero (hz i hi)
    let : Subsingleton (Power (Laurent K D) (A.rank i)) := (A.coordinates i).symm.injective.subsingleton
    change IsZero (ModuleCat.of (Laurent K D) (Power (Laurent K D) (A.rank i)))
    exact ModuleCat.isZero_of_subsingleton _

end
end Decoupling.HighDim.StableFree.Effective.CochainProgram
