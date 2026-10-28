import Decoupling.HighDim.StableFreeCokernel
import Decoupling.HighDim.CochainCokernel
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# Finite free stable check-cokernel construction from bounded complexes

HD012, Appendix C4. The negative part of each actual cochain complex is
converted to a finite free resolution of its actual check cokernel. The
constructed Schanuel map then absorbs the genuine projective complement.
This module reuses only the elementary cokernel/homotopy identities from
`CochainCokernel`, not its Laurent finite-projective-freeness theorem.
-/

namespace Decoupling.HighDim.StableFree

open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
noncomputable section
variable {R : Type u} [CommRing R]

/-- Chosen coordinates for already free terms of an input complex. -/
structure Coordinates (C : CochainComplex (ModuleCat.{u} R) ℤ) where
  rank : ℤ → ℕ
  equiv : ∀ i, C.X i ≃ₗ[R] Power R (rank i)

/-- The actual quotient augmentation and negative differentials, with the
original supplied free coordinates. -/
def checkSequence (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (c : Coordinates C) (he : ∀ i : ℤ, i ≤ 0 → C.ExactAt i) :
    Sequence (ModuleCat.of R (CochainCokernel.CheckCokernel C)) where
  X n := C.X (1 - (n : ℤ))
  rank n := c.rank (1 - (n : ℤ))
  coordinates n := c.equiv (1 - (n : ℤ))
  d n := (C.d (1 - (n + 1 : ℕ)) (1 - (n : ℤ))).hom
  ε := (LinearMap.range (C.d 0 1).hom).mkQ
  surjective := (LinearMap.range (C.d 0 1).hom).mkQ_surjective
  exact_zero := by simp
  exact_succ n := by
    have h := he (1 - (n + 1 : ℕ)) (by omega)
    rw [exactAt_iff' C (1 - (n + 2 : ℕ)) (1 - (n + 1 : ℕ)) (1 - (n : ℤ))
      (by apply (ComplexShape.up ℤ).prev_eq'; change (1 - ((n + 2 : ℕ) : ℤ)) + 1 = 1 - ((n + 1 : ℕ) : ℤ); omega)
      (by apply (ComplexShape.up ℤ).next_eq'; change (1 - ((n + 1 : ℕ) : ℤ)) + 1 = 1 - (n : ℤ); omega)] at h
    exact (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp h

/-- A strict lower degree bound supplies the actual termination of the
resolution; two extra indices include degrees one and zero. -/
def checkResolution (C : CochainComplex (ModuleCat.{u} R) ℤ)
    (c : Coordinates C) (he : ∀ i : ℤ, i ≤ 0 → C.ExactAt i)
    (l : ℕ) [C.IsStrictlyGE (-(l : ℤ))] :
    Resolution R (l + 2) (ModuleCat.of R (CochainCokernel.CheckCokernel C)) :=
  (checkSequence C c he).resolution (l + 2) (by
    intro n hn
    exact C.isZero_of_isStrictlyGE (-(l : ℤ)) (1 - (n : ℤ)) (by omega))

/-- Input exactness in all nonpositive degrees is the usual native `IsGE 1`. -/
theorem nonpositive_exact (C : CochainComplex (ModuleCat.{u} R) ℤ) [C.IsGE 1]
    (i : ℤ) (hi : i ≤ 0) : C.ExactAt i := C.exactAt_of_isGE 1 i (by omega)

/-- Known finite free terms admit finite coordinates; this selects bases
only for the supplied terms, never for the projective complement. -/
def Coordinates.ofFiniteFree (C : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ i, Module.Finite R (C.X i)] [∀ i, Module.Free R (C.X i)] : Coordinates C where
  rank i := Fintype.card (Module.Free.ChooseBasisIndex R (C.X i))
  equiv i := StableCokernel.finiteFreeEquiv (C.X i)

end
end Decoupling.HighDim.StableFree
