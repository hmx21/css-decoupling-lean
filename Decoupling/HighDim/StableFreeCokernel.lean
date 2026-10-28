import Decoupling.HighDim.StableFreeSequence

/-!
# Stable check-cokernel isomorphism without making the complement free

HD012, `drafts/appendix.tex:945–965`.  The actual split retraction supplies
`N ⊕ P ≃ M ⊕ ker ρ`.  Finite free resolutions of `M,N` then supply the
extra free block and its explicit isomorphism by generalized Schanuel.
Only already specified free terms are coordinated. No basis of `ker ρ`
and no theorem making finite projectives free occurs in this proof.
-/

namespace Decoupling.HighDim.StableFree

universe u
noncomputable section
variable {R : Type u} [Ring R]
variable {M N P Q : ModuleCat.{u} R} {n : ℕ}

/-- The extra number of free coordinates adjoined to the complement. -/
def extraRank (F : Resolution R n M) (G : Resolution R n N) : ℕ :=
  (G.ranks F).2

/-- The target free rank; every summand is a known free-term rank. -/
def targetRank (F : Resolution R n M) (G : Resolution R n N) (p : ℕ) : ℕ :=
  p + (G.ranks F).1

/-- The actual projective complement is stably free, with an explicit
isomorphism made solely from the given resolutions and projective lifts. -/
def complementEquiv (F : Resolution R n M) (G : Resolution R n N)
    (p : ℕ) (cP : P ≃ₗ[R] Power R p) [Module.Projective R Q]
    (e : (N × P) ≃ₗ[R] (M × Q)) :
    (Q × Power R (extraRank F G)) ≃ₗ[R] Power R (targetRank F G p) := by
  letI : Module.Free R P := Module.Free.of_equiv cP.symm
  exact (G.stabilize F P Q e).symm.trans
    ((cP.prodCongr (LinearEquiv.refl _ _)).trans (powerAdd p (G.ranks F).1))

/-- Add precisely the free block from `complementEquiv` to the split
retraction isomorphism. This is the stable-cokernel map used by the lift. -/
def absorb (F : Resolution R n M) (G : Resolution R n N)
    (p : ℕ) (cP : P ≃ₗ[R] Power R p) [Module.Projective R Q]
    (e : (N × P) ≃ₗ[R] (M × Q)) :
    (N × Power R (p + extraRank F G)) ≃ₗ[R]
      (M × Power R (targetRank F G p)) :=
  ((LinearEquiv.refl R N).prodCongr
    (((cP.prodCongr (LinearEquiv.refl R (Power R (extraRank F G)))).trans
      (powerAdd p (extraRank F G))).symm)).trans
    ((LinearEquiv.prodAssoc R N P (Power R (extraRank F G))).symm.trans
      ((e.prodCongr (LinearEquiv.refl _ _)).trans
        ((LinearEquiv.prodAssoc R M Q (Power R (extraRank F G))).trans
          ((LinearEquiv.refl R M).prodCongr (complementEquiv F G p cP e)))))

section ActualComplement
variable {E : ModuleCat.{u} R}
  (f : M →ₗ[R] N) (g : N →ₗ[R] M)
  (ξM : M →ₗ[R] P) (ζM : P →ₗ[R] M)
  (ξN : N →ₗ[R] E) (ζN : E →ₗ[R] N)
  (hM : LinearMap.id - g.comp f = ζM.comp ξM)
  (hN : LinearMap.id - f.comp g = ζN.comp ξN)

/-- Specialization to the genuine `ker ρ` constructed from homotopy errors.
The projectivity premise for that kernel is proved by its actual retract. -/
def actualComplementEquiv (F : Resolution R n M) (G : Resolution R n N)
    (p : ℕ) (cP : P ≃ₗ[R] Power R p) [Module.Projective R E] :
    (StableCokernel.Complement g ζM × Power R (extraRank F G)) ≃ₗ[R]
      Power R (targetRank F G p) := by
  letI : Module.Free R P := Module.Free.of_equiv cP.symm
  letI : Module.Projective R (StableCokernel.Complement g ζM) :=
    StableCokernel.complement_projective f g ξM ζM ξN ζN hM hN
  exact complementEquiv (Q := ModuleCat.of R (StableCokernel.Complement g ζM)) F G p cP
    (StableCokernel.stableProjectiveEquiv f g ξM ζM hM)

/-- The stable cokernel isomorphism with no finite-projective-freeness input. -/
def actualStableEquiv (F : Resolution R n M) (G : Resolution R n N)
    (p : ℕ) (cP : P ≃ₗ[R] Power R p) [Module.Projective R E] :
    (N × Power R (p + extraRank F G)) ≃ₗ[R]
      (M × Power R (targetRank F G p)) := by
  letI : Module.Free R P := Module.Free.of_equiv cP.symm
  letI : Module.Projective R (StableCokernel.Complement g ζM) :=
    StableCokernel.complement_projective f g ξM ζM ξN ζN hM hN
  exact absorb (Q := ModuleCat.of R (StableCokernel.Complement g ζM)) F G p cP
    (StableCokernel.stableProjectiveEquiv f g ξM ζM hM)

end ActualComplement
end
end Decoupling.HighDim.StableFree
