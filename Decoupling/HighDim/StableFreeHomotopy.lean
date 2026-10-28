import Decoupling.HighDim.StableFreeCochain

/-!
# The C4 stable-cokernel construction with explicit ranks and no Swan step

The input is an actual homotopy equivalence of the two bounded finite free
complexes. Their nonpositive exactness supplies the actual check-cokernel
resolutions. All quotient comparison maps and error factorizations are
extracted from that homotopy, and the genuine kernel complement is absorbed
by the generalized Schanuel isomorphism.
-/

namespace Decoupling.HighDim.StableFree

open CategoryTheory CategoryTheory.Limits HomologicalComplex
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R]
variable {C T : CochainComplex (ModuleCat.{u} R) ℤ}

/-- All ranks used in the extra stabilization are computable from the
original free terms in degrees `1,0,-1,…,-l`. -/
def cochainRanks (cC : Coordinates C) (cT : Coordinates T) (l : ℕ) : ℕ × ℕ :=
  parityRanks (l + 2) (fun n => cT.rank (1 - (n : ℤ)))
    (fun n => cC.rank (1 - (n : ℤ)))

/-- The actual stable check-cokernel map; no basis of the projective kernel
is computed or assumed. Its two stabilizing ranks are explicit. -/
def homotopyStableEquiv (e : HomotopyEquiv C T)
    (cC : Coordinates C) (cT : Coordinates T) (l : ℕ)
    [C.IsStrictlyGE (-(l : ℤ))] [T.IsStrictlyGE (-(l : ℤ))]
    [C.IsGE 1] [T.IsGE 1] :
    (CochainCokernel.CheckCokernel T ×
      Power R (cC.rank 2 + (cochainRanks cC cT l).2)) ≃ₗ[R]
    (CochainCokernel.CheckCokernel C ×
      Power R (cC.rank 2 + (cochainRanks cC cT l).1)) := by
  let F := checkResolution C cC (nonpositive_exact C) l
  let G := checkResolution T cT (nonpositive_exact T) l
  have hr : G.ranks F = cochainRanks cC cT l :=
    Sequence.resolution_ranks (checkSequence T cT (nonpositive_exact T))
      (checkSequence C cC (nonpositive_exact C)) (l + 2) _ _
  let f := StableCokernel.cokernelMap (C.d 0 1).hom (T.d 0 1).hom
    (e.hom.f 0).hom (e.hom.f 1).hom (CochainCokernel.map_comm e.hom)
  let g := StableCokernel.cokernelMap (T.d 0 1).hom (C.d 0 1).hom
    (e.inv.f 0).hom (e.inv.f 1).hom (CochainCokernel.map_comm e.inv)
  let ξM := StableCokernel.cokernelDifferential (C.d 0 1).hom (C.d 1 2).hom
    (CochainCokernel.differential_comp C)
  let ξN := StableCokernel.cokernelDifferential (T.d 0 1).hom (T.d 1 2).hom
    (CochainCokernel.differential_comp T)
  let ζM := (LinearMap.range (C.d 0 1).hom).mkQ.comp
    (e.homotopyHomInvId.symm.hom 2 1).hom
  let ζN := (LinearMap.range (T.d 0 1).hom).mkQ.comp
    (e.homotopyInvHomId.symm.hom 2 1).hom
  have hM : LinearMap.id - g.comp f = ζM.comp ξM :=
    StableCokernel.cokernel_error_factorization
      (C.d 0 1).hom (C.d 1 2).hom (T.d 0 1).hom
      (CochainCokernel.differential_comp C)
      (e.inv.f 0).hom (e.inv.f 1).hom (e.hom.f 0).hom (e.hom.f 1).hom
      (CochainCokernel.map_comm e.inv) (CochainCokernel.map_comm e.hom)
      (e.homotopyHomInvId.symm.hom 1 0).hom (e.homotopyHomInvId.symm.hom 2 1).hom
      (CochainCokernel.homotopy_error e.hom e.inv e.homotopyHomInvId.symm)
  have hN : LinearMap.id - f.comp g = ζN.comp ξN :=
    StableCokernel.cokernel_error_factorization
      (T.d 0 1).hom (T.d 1 2).hom (C.d 0 1).hom
      (CochainCokernel.differential_comp T)
      (e.hom.f 0).hom (e.hom.f 1).hom (e.inv.f 0).hom (e.inv.f 1).hom
      (CochainCokernel.map_comm e.hom) (CochainCokernel.map_comm e.inv)
      (e.homotopyInvHomId.symm.hom 1 0).hom (e.homotopyInvHomId.symm.hom 2 1).hom
      (CochainCokernel.homotopy_error e.inv e.hom e.homotopyInvHomId.symm)
  letI : Module.Free R (T.X 2) := Module.Free.of_equiv (cT.equiv 2).symm
  have result := actualStableEquiv
    (M := ModuleCat.of R (CochainCokernel.CheckCokernel C))
    (N := ModuleCat.of R (CochainCokernel.CheckCokernel T))
    (P := C.X 2) (E := T.X 2) f g ξM ζM ξN ζN hM hN F G (cC.rank 2) (cC.equiv 2)
  change (CochainCokernel.CheckCokernel T × Power R (cC.rank 2 + (G.ranks F).2)) ≃ₗ[R]
    (CochainCokernel.CheckCokernel C × Power R (cC.rank 2 + (G.ranks F).1)) at result
  rw [hr] at result
  exact result

/-- A convenient existential wrapper for already finite free input complexes.
The only basis selections here are for those input terms. -/
theorem exists_stableEquiv_of_homotopyEquiv (e : HomotopyEquiv C T) (l : ℕ)
    [C.IsStrictlyGE (-(l : ℤ))] [T.IsStrictlyGE (-(l : ℤ))]
    [C.IsGE 1] [T.IsGE 1]
    [∀ i, Module.Finite R (C.X i)] [∀ i, Module.Free R (C.X i)]
    [∀ i, Module.Finite R (T.X i)] [∀ i, Module.Free R (T.X i)] :
    ∃ a b : ℕ, Nonempty
      ((CochainCokernel.CheckCokernel T × Power R b) ≃ₗ[R]
        (CochainCokernel.CheckCokernel C × Power R a)) := by
  let cC := Coordinates.ofFiniteFree C
  let cT := Coordinates.ofFiniteFree T
  exact ⟨_, _, ⟨homotopyStableEquiv e cC cT l⟩⟩

end
end Decoupling.HighDim.StableFree
