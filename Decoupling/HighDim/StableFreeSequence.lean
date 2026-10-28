import Decoupling.HighDim.StableFreeResolution
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Actual finite exact sequences supply the Schanuel input

HD012, Appendix C4. Every resolution term has supplied finite free
coordinates. The recursion uses actual kernel submodules and the exactness
of the supplied differentials. No projective-complement basis is chosen.
-/

namespace Decoupling.HighDim.StableFree

open CategoryTheory CategoryTheory.Limits
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [Ring R]

/-- An augmented exact sequence of explicitly coordinated finite free modules. -/
structure Sequence (M : ModuleCat.{u} R) where
  X : ℕ → ModuleCat.{u} R
  rank : ℕ → ℕ
  coordinates : ∀ n, X n ≃ₗ[R] Power R (rank n)
  d : ∀ n, X (n + 1) →ₗ[R] X n
  ε : X 0 →ₗ[R] M
  surjective : Function.Surjective ε
  exact_zero : LinearMap.range (d 0) = LinearMap.ker ε
  exact_succ : ∀ n, LinearMap.range (d (n + 1)) = LinearMap.ker (d n)

namespace Sequence
variable {M : ModuleCat.{u} R} (A : Sequence M)

/-- The next actual augmentation maps onto the actual first syzygy. -/
def tailMap : A.X 1 →ₗ[R] LinearMap.ker A.ε :=
  (A.d 0).codRestrict (LinearMap.ker A.ε) (by
    intro x
    rw [← A.exact_zero]
    exact ⟨x, rfl⟩)

theorem tailMap_surjective : Function.Surjective A.tailMap := by
  intro x
  have hx : (x : A.X 0) ∈ LinearMap.range (A.d 0) := by
    rw [A.exact_zero]
    exact x.property
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

/-- Dropping the head term preserves actual exactness. -/
def tail : Sequence (ModuleCat.of R (LinearMap.ker A.ε)) where
  X n := A.X (n + 1)
  rank n := A.rank (n + 1)
  coordinates n := A.coordinates (n + 1)
  d n := A.d (n + 1)
  ε := A.tailMap
  surjective := A.tailMap_surjective
  exact_zero := by
    rw [A.exact_succ 0]
    ext x
    change A.d 0 x = 0 ↔ A.tailMap x = 0
    exact ⟨fun hx => Subtype.ext hx, fun hx => congrArg Subtype.val hx⟩
  exact_succ n := A.exact_succ (n + 1)

/-- Convert a bounded augmented sequence into the recursive exact resolution.
The zero-length case derives that the augmented module is actually zero. -/
def resolution : (length : ℕ) → {M : ModuleCat.{u} R} → (A : Sequence M) →
    (∀ n, length ≤ n → IsZero (A.X n)) → Resolution R length M
  | 0, M, A, h => by
      letI : Subsingleton (A.X 0) := ModuleCat.subsingleton_of_isZero (h 0 (by omega))
      letI : Subsingleton M := A.surjective.subsingleton
      exact .zero (LinearEquiv.ofSubsingleton _ _)
  | n + 1, _, A, h =>
      .step (A.X 0) (A.rank 0) (A.coordinates 0) A.ε A.surjective
        (resolution n A.tail (by intro i hi; exact h (i+1) (by omega)))

end Sequence

/-- Pure arithmetic description of the two parity rank totals. -/
def parityRanks : ℕ → (ℕ → ℕ) → (ℕ → ℕ) → ℕ × ℕ
  | 0, _, _ => (0,0)
  | n+1, r, s =>
      let t := parityRanks n (fun i => r (i+1)) (fun i => s (i+1))
      (r 0 + t.2, s 0 + t.1)

/-- The ranks in the constructed isomorphism depend only on the supplied
free term ranks, not on the chosen linear lifts or a basis of the complement. -/
theorem Sequence.resolution_ranks {M N : ModuleCat.{u} R}
    (A : Sequence M) (B : Sequence N) (n : ℕ)
    (hA : ∀ i, n ≤ i → IsZero (A.X i)) (hB : ∀ i, n ≤ i → IsZero (B.X i)) :
    (A.resolution n hA).ranks (B.resolution n hB) = parityRanks n A.rank B.rank := by
  induction n generalizing M N with
  | zero => rfl
  | succ n ih =>
    simp only [Sequence.resolution, Resolution.ranks, parityRanks]
    rw [ih A.tail B.tail]
    rfl

end
end Decoupling.HighDim.StableFree
