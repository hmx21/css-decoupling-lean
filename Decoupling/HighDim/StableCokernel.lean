import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.Tactic.Abel

/-!
# Absorbing homotopy errors into projective summands

This module formalizes the module-theoretic argument in `drafts/appendix.tex`,
lines 511–577. For maps `f : M → N` and `g : N → M`, the two errors from being
inverse are assumed to factor through modules `P` and `Q`. The complement is
the actual kernel of `(g, ζM) : N × P → M`; it is constructed, not supplied.
It is a retract of `Q × P`, hence finite and projective when `P,Q` are finite
projective. An explicitly conditional corollary converts this to finite free
stabilization. The Laurent-ring freeness theorem and the derivation of these
error factorizations from a profile equivalence remain separate interfaces.
-/

namespace Decoupling.HighDim.StableCokernel

universe u v

variable {R : Type u} [Ring R]
variable {M N P Q : Type v}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
  [Module R M] [Module R N] [Module R P] [Module R Q]

/-- The section used to absorb the first error. -/
def sectionMap (f : M →ₗ[R] N) (ξM : M →ₗ[R] P) : M →ₗ[R] N × P :=
  f.prod ξM

/-- The retraction whose kernel is the required complement. -/
def retraction (g : N →ₗ[R] M) (ζM : P →ₗ[R] M) : N × P →ₗ[R] M :=
  g.coprod ζM

theorem retraction_section
    (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (ξM : M →ₗ[R] P) (ζM : P →ₗ[R] M)
    (hM : LinearMap.id - g.comp f = ζM.comp ξM) :
    (retraction g ζM).comp (sectionMap f ξM) = LinearMap.id := by
  ext m
  have h := DFunLike.congr_fun hM m
  change m - g (f m) = ζM (ξM m) at h
  change g (f m) + ζM (ξM m) = m
  rw [← h]
  abel

section Split

variable (i : M →ₗ[R] N) (r : N →ₗ[R] M)
  (h : r.comp i = LinearMap.id)

/-- Projection onto the actual kernel of a split retraction. -/
def kernelProjection : N →ₗ[R] LinearMap.ker r :=
  (LinearMap.id - i.comp r).codRestrict (LinearMap.ker r) (by
    intro n
    have hn := DFunLike.congr_fun h (r n)
    change r (i (r n)) = r n at hn
    change r (n - i (r n)) = 0
    rw [map_sub, hn, sub_self])

@[simp] theorem kernelProjection_apply_coe (n : N) :
    (kernelProjection i r h n : N) = n - i (r n) := rfl

@[simp] theorem kernelProjection_subtype (n : LinearMap.ker r) :
    kernelProjection i r h n = n := by
  apply Subtype.ext
  change (n : N) - i (r n) = n
  rw [n.property, map_zero, sub_zero]

/-- A split retraction decomposes the source as its target plus its kernel. -/
def splitEquiv : N ≃ₗ[R] (M × LinearMap.ker r) where
  toLinearMap := r.prod (kernelProjection i r h)
  invFun x := i x.1 + x.2
  left_inv n := by
    change i (r n) + (n - i (r n)) = n
    abel
  right_inv x := by
    obtain ⟨m, n⟩ := x
    apply Prod.ext
    · change r (i m + n) = m
      have hm := DFunLike.congr_fun h m
      change r (i m) = m at hm
      rw [map_add, hm, n.property, add_zero]
    · apply Subtype.ext
      change i m + (n : N) - i (r (i m + n)) = n
      have hm := DFunLike.congr_fun h m
      change r (i m) = m at hm
      rw [map_add, hm, n.property, add_zero]
      abel

end Split

section Complement

variable (f : M →ₗ[R] N) (g : N →ₗ[R] M)
  (ξM : M →ₗ[R] P) (ζM : P →ₗ[R] M)
  (ξN : N →ₗ[R] Q) (ζN : Q →ₗ[R] N)
  (hM : LinearMap.id - g.comp f = ζM.comp ξM)
  (hN : LinearMap.id - f.comp g = ζN.comp ξN)

/-- The genuine kernel complement; no choice of a complement is assumed. -/
abbrev Complement := LinearMap.ker (retraction g ζM)

/-- Embed the complement in the sum of the error-factorization modules. -/
def complementEmbedding : Complement g ζM →ₗ[R] Q × P :=
  ((ξN.comp (LinearMap.fst R N P)).prod (LinearMap.snd R N P)).comp
    (LinearMap.ker (retraction g ζM)).subtype

/-- The unprojected candidate inverse of `complementEmbedding`. -/
def complementLift : Q × P →ₗ[R] N × P :=
  ((ζN.comp (LinearMap.fst R Q P) -
    f.comp (ζM.comp (LinearMap.snd R Q P))).prod (LinearMap.snd R Q P))

include hN in
theorem complementLift_embedding :
    (complementLift f ζM ζN).comp (complementEmbedding g ζM ξN) =
      (LinearMap.ker (retraction g ζM)).subtype := by
  apply LinearMap.ext
  intro l
  apply Prod.ext
  · change ζN (ξN l.val.1) - f (ζM l.val.2) = l.val.1
    have he := DFunLike.congr_fun hN l.val.1
    change l.val.1 - f (g l.val.1) = ζN (ξN l.val.1) at he
    have hk := l.property
    change g l.val.1 + ζM l.val.2 = 0 at hk
    have hg : g l.val.1 = -ζM l.val.2 := eq_neg_of_add_eq_zero_left hk
    rw [← he, hg, map_neg]
    abel
  · rfl

/-- Projecting the lift produces a map into the kernel complement. -/
def complementRetraction : Q × P →ₗ[R] Complement g ζM :=
  (kernelProjection (sectionMap f ξM) (retraction g ζM)
    (retraction_section f g ξM ζM hM)).comp (complementLift f ζM ζN)

include hN in
theorem complement_retract :
    (complementRetraction f g ξM ζM ζN hM).comp
      (complementEmbedding g ζM ξN) = LinearMap.id := by
  rw [complementRetraction, LinearMap.comp_assoc,
    complementLift_embedding f g ζM ξN ζN hN]
  apply LinearMap.ext
  intro l
  exact kernelProjection_subtype _ _ (retraction_section f g ξM ζM hM) l

include f ξM ξN ζN hM hN

/-- The constructed complement is projective: it is a retract of `Q × P`. -/
theorem complement_projective [Module.Projective R P] [Module.Projective R Q] :
    Module.Projective R (Complement g ζM) :=
  Module.Projective.of_split (complementEmbedding g ζM ξN)
    (complementRetraction f g ξM ζM ζN hM)
    (complement_retract f g ξM ζM ξN ζN hM hN)

/-- Finite generation follows from the explicit surjection `Q × P → L`. -/
theorem complement_finite [Module.Finite R P] [Module.Finite R Q] :
    Module.Finite R (Complement g ζM) := by
  apply Module.Finite.of_surjective (complementRetraction f g ξM ζM ζN hM)
  intro l
  refine ⟨complementEmbedding g ζM ξN l, ?_⟩
  exact DFunLike.congr_fun (complement_retract f g ξM ζM ξN ζN hM hN) l

/-- The stable isomorphism before the projective complement is made free. -/
def stableProjectiveEquiv : (N × P) ≃ₗ[R] (M × Complement g ζM) :=
  splitEquiv (sectionMap f ξM) (retraction g ζM)
    (retraction_section f g ξM ζM hM)

end Complement

section FreeStabilization

/-- A finite free module is explicitly equivalent to a finite power of the ring. -/
noncomputable def finiteFreeEquiv (L : Type v) [AddCommGroup L] [Module R L]
    [Module.Finite R L] [Module.Free R L] :
    L ≃ₗ[R] (Fin (Fintype.card (Module.Free.ChooseBasisIndex R L)) → R) :=
  ((Module.Free.chooseBasis R L).reindex (Fintype.equivFin _)).equivFun

/-- Conditional ring-theoretic interface: once finite projectives over `R` are
known to be free, the explicitly constructed complement gives free summands.
The hypothesis `hfree` must be discharged for the Laurent ring before this
lemma can be used to obtain the paper's unconditional decoupling statement. -/
theorem exists_stableFreeEquiv
    (f : M →ₗ[R] N) (g : N →ₗ[R] M)
    (ξM : M →ₗ[R] P) (ζM : P →ₗ[R] M)
    (ξN : N →ₗ[R] Q) (ζN : Q →ₗ[R] N)
    (hM : LinearMap.id - g.comp f = ζM.comp ξM)
    (hN : LinearMap.id - f.comp g = ζN.comp ξN)
    [Module.Finite R P] [Module.Free R P]
    [Module.Finite R Q] [Module.Projective R Q]
    (hfree : ∀ (L : Type v) [AddCommGroup L] [Module R L]
      [Module.Finite R L] [Module.Projective R L], Module.Free R L) :
    ∃ a b : ℕ, Nonempty ((N × (Fin b → R)) ≃ₗ[R] (M × (Fin a → R))) := by
  let := complement_finite f g ξM ζM ξN ζN hM hN
  let := complement_projective f g ξM ζM ξN ζN hM hN
  let := hfree (Complement g ζM)
  refine ⟨Fintype.card (Module.Free.ChooseBasisIndex R (Complement g ζM)),
    Fintype.card (Module.Free.ChooseBasisIndex R P), ?_⟩
  exact ⟨((LinearEquiv.refl R N).prodCongr (finiteFreeEquiv P).symm).trans
    ((stableProjectiveEquiv f g ξM ζM hM).trans
      ((LinearEquiv.refl R M).prodCongr (finiteFreeEquiv (Complement g ζM))))⟩

end FreeStabilization

end Decoupling.HighDim.StableCokernel
