import Decoupling.HighDim.SchreyerModule

/-!
# Coordinate data of a finite free resolution of an actual polynomial submodule

All differentials and the augmentation are actual polynomial matrices.
This is an output specification; the Schreyer construction must prove
existence and supply every exactness/length field. No projective-module
basis or resolution oracle is an input to the final construction.
-/
namespace Decoupling.HighDim.SchreyerResolution
open SchreyerModule Matrix
variable {K : Type*} [Field K] {D r : ℕ}

structure Data (N : Submodule (Poly K D) (Vec K D r)) (length : ℕ) where
  rank : ℕ → ℕ
  d : ∀ k : ℕ, Matrix (Fin (rank k)) (Fin (rank (k+1))) (Poly K D)
  augmentation : Matrix (Fin r) (Fin (rank 0)) (Poly K D)
  range_augmentation : LinearMap.range augmentation.mulVecLin=N
  exact_zero : LinearMap.ker augmentation.mulVecLin=LinearMap.range (d 0).mulVecLin
  exact_succ : ∀ k, LinearMap.ker (d k).mulVecLin=LinearMap.range (d (k+1)).mulVecLin
  zero_above : ∀ k, length<k → rank k=0

namespace Data
variable {N : Submodule (Poly K D) (Vec K D r)} {length : ℕ} (A : Data N length)

theorem augmentation_comp : A.augmentation*A.d 0=0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [← Matrix.mulVec_mulVec,Matrix.zero_mulVec]
  have hv : A.d 0 *ᵥ v ∈ LinearMap.range (A.d 0).mulVecLin := ⟨v,rfl⟩
  rw [← A.exact_zero] at hv
  exact hv

theorem d_comp (k : ℕ) : A.d k*A.d (k+1)=0 := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [← Matrix.mulVec_mulVec,Matrix.zero_mulVec]
  have hv : A.d (k+1) *ᵥ v ∈ LinearMap.range (A.d (k+1)).mulVecLin := ⟨v,rfl⟩
  rw [← A.exact_succ k] at hv
  exact hv

end Data
end Decoupling.HighDim.SchreyerResolution
