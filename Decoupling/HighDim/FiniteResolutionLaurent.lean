import Decoupling.HighDim.FiniteResolution
import Decoupling.HighDim.DegreeBound

/-!
# Finite free resolutions over the actual Laurent ring

The Noetherianity, projective-dimension bound, and finite-projective
freeness of this ring are proved dependencies. No resolution-existence or
freeness hypothesis is placed on a CSS code.
-/

namespace Decoupling.HighDim.FiniteResolution

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u
noncomputable section

variable {K : Type u} [Field K] {D : ℕ}

/-- Every finite projective term of a constructed Laurent resolution is free. -/
theorem Data.free {M : ModuleCat.{u} (Laurent K D)} {n : ℕ} (A : Data M n) (k : ℕ) :
    Module.Free (Laurent K D) (A.X k) := by
  have : Module.Projective (Laurent K D) (A.X k) :=
    (IsProjective.iff_projective (A.X k)).mpr (A.projective k)
  exact RingDimension.finite_projective_free K D (A.X k)

/-- A chosen resolution with the sharp supplied projective-dimension bound.
Existence is proved recursively by finite free covers in `exists_data`. -/
def ofDimensionBound (n : ℕ) (M : ModuleCat.{u} (Laurent K D))
    [Module.Finite (Laurent K D) M] [HasProjectiveDimensionLE M n] : Data M n :=
  (exists_data n M).some

/-- A finite module over the actual `D`-variable Laurent ring has a bounded
finite free resolution of length at most `D`. -/
def laurent (M : ModuleCat.{u} (Laurent K D)) [Module.Finite (Laurent K D) M] : Data M D := by
  letI := RingDimension.projectiveDimensionLE K D M
  exact ofDimensionBound D M

/-- The same result in mathlib's native projective-resolution type, with
termwise finite freeness and the actual length bound. -/
theorem exists_native_free (M : ModuleCat.{u} (Laurent K D))
    [Module.Finite (Laurent K D) M] :
    ∃ A : ProjectiveResolution M,
      (∀ k, Module.Finite (Laurent K D) (A.complex.X k)) ∧
      (∀ k, Module.Free (Laurent K D) (A.complex.X k)) ∧
      (∀ k, D < k → IsZero (A.complex.X k)) := by
  let A := laurent M
  exact ⟨A.toProjectiveResolution, A.finite, A.free, A.zero_above⟩

end

end Decoupling.HighDim.FiniteResolution
