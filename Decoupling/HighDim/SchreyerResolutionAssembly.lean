import Decoupling.HighDim.SchreyerResolutionData

/-!
# Joining actual free polynomial matrices into a finite resolution

The zero-length case uses an injective actual augmentation. The successor
case attaches a resolution of its actual kernel. All exactness equations
are preserved as equalities of ranges and kernels of the displayed matrices.
-/
namespace Decoupling.HighDim.SchreyerResolution
open SchreyerModule Matrix
noncomputable section
variable {K : Type*} [Field K] {D r s n : ℕ}

def terminalRank (s : ℕ) : ℕ → ℕ
  | 0 => s
  | _+1 => 0

/-- A free generating family produces a resolution of length zero. -/
def terminal {N : Submodule (Poly K D) (Vec K D r)}
    (A₀ : Matrix (Fin r) (Fin s) (Poly K D))
    (hrange : LinearMap.range A₀.mulVecLin=N)
    (hker : LinearMap.ker A₀.mulVecLin=⊥) : Data N 0 where
  rank := terminalRank s
  d _ := 0
  augmentation := A₀
  range_augmentation := hrange
  exact_zero := by
    change LinearMap.ker A₀.mulVecLin=LinearMap.range (0 : Matrix (Fin s) (Fin 0) (Poly K D)).mulVecLin
    have he : (0 : Matrix (Fin s) (Fin 0) (Poly K D)).mulVecLin=0 := by
      apply LinearMap.ext
      intro v
      exact Matrix.zero_mulVec v
    rw [he,LinearMap.range_zero]
    exact hker
  exact_succ k := by
    have : Subsingleton (Fin (terminalRank s (k+1)) → Poly K D) := by
      change Subsingleton (Fin 0 → Poly K D)
      infer_instance
    have hk : LinearMap.ker (0 : Matrix (Fin (terminalRank s k))
        (Fin (terminalRank s (k+1))) (Poly K D)).mulVecLin=⊥ :=
      LinearMap.ker_eq_bot_of_injective (Function.injective_of_subsingleton _)
    simpa using hk
  zero_above k hk := by
    cases k with
    | zero => omega
    | succ k => rfl

def prependRank (s : ℕ) (tail : ℕ → ℕ) : ℕ → ℕ
  | 0 => s
  | k+1 => tail k

def prependDifferential (A₀ : Matrix (Fin r) (Fin s) (Poly K D))
    (A : Data (LinearMap.ker A₀.mulVecLin) n) :
    ∀ k, Matrix (Fin (prependRank s A.rank k))
      (Fin (prependRank s A.rank (k+1))) (Poly K D)
  | 0 => A.augmentation
  | k+1 => A.d k

/-- Attaching the actual kernel resolution increases the length by exactly one. -/
def prepend {N : Submodule (Poly K D) (Vec K D r)}
    (A₀ : Matrix (Fin r) (Fin s) (Poly K D))
    (hrange : LinearMap.range A₀.mulVecLin=N)
    (A : Data (LinearMap.ker A₀.mulVecLin) n) : Data N (n+1) where
  rank := prependRank s A.rank
  d := prependDifferential A₀ A
  augmentation := A₀
  range_augmentation := hrange
  exact_zero := A.range_augmentation.symm
  exact_succ k := by
    cases k with
    | zero => exact A.exact_zero
    | succ k => exact A.exact_succ k
  zero_above k hk := by
    cases k with
    | zero => omega
    | succ k => exact A.zero_above k (by omega)

end
end Decoupling.HighDim.SchreyerResolution
