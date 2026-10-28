import Decoupling.HighDim.ProfileStabilityCircuit

/-!
# Lemma 5: combined stable physical equivalences preserve the profile

Both source and target may have different numbers of product-state ancillas
and identity X checks. The hypothesis is the actual two-sector stabilizer
transport by a finite physical SUM/SWAP word. All intermediate module and
profile isomorphisms are constructed here.
-/

namespace Decoupling.HighDim.ProfileStability

open CategoryTheory Matrix
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [CommRing K] {D : ℕ}
local notation "R" => Laurent K D
variable {Q C A B I : Type} [Fintype C] [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B]

/-- The composite of all allowed additions has the original actual profile. -/
def stabilizedProfileIso (H : Matrix C Q R) :
    matrixProfile (StableCSS.H_X (A := A) (B := B)
      (StableCSS.identityChecks (A := I) H)) ≅ matrixProfile H :=
  ancillaProfileIso (StableCSS.identityChecks (A := I) H) ≪≫ identityChecksProfileIso H

variable {Q' C' A' B' I' Z Z' : Type}
  [Fintype Q] [DecidableEq Q] [Fintype Q'] [DecidableEq Q']
  [Fintype C'] [Fintype A'] [Fintype B'] [Fintype I'] [Fintype Z] [Fintype Z']
  [DecidableEq A'] [DecidableEq B']

/-- Full profile invariance under stable SUM/SWAP equivalence, with actual
block stabilizer matrices on both sides and no profile-isomorphism input. -/
def stableCircuitProfileIso (HC : Matrix C Q R) (HT : Matrix C' Q' R)
    (BC : Matrix Q Z R) (BT : Matrix Q' Z' R)
    (gates : List (Circuit.Layer K D ((Q' ⊕ A') ⊕ B')))
    (e : ((Q ⊕ A) ⊕ B) ≃ ((Q' ⊕ A') ⊕ B'))
    (h : PhysicalIsomorphism.Transports gates e
      (StableCSS.H_X (A := A) (B := B) (StableCSS.identityChecks (A := I) HC))
      (StableCSS.H_X (A := A') (B := B') (StableCSS.identityChecks (A := I') HT))
      (StableCSS.H_Z_dagger (A := A) (B := B) BC)
      (StableCSS.H_Z_dagger (A := A') (B := B') BT)) :
    matrixProfile HC ≅ matrixProfile HT :=
  (stabilizedProfileIso (A := A) (B := B) (I := I) HC).symm ≪≫
    circuitProfileIso gates e _ _ _ _ h ≪≫
    stabilizedProfileIso (A := A') (B := B') (I := I') HT

/-- The same stable invariance stated on the manuscript's actual CSS profile. -/
def cssStableCircuitProfileIso {q s r q' s' r' : ℕ}
    (c : CSS.Checks K D q s r) (d : CSS.Checks K D q' s' r')
    (gates : List (Circuit.Layer K D ((Fin q' ⊕ A') ⊕ B')))
    (e : ((Fin q ⊕ A) ⊕ B) ≃ ((Fin q' ⊕ A') ⊕ B'))
    (h : PhysicalIsomorphism.Transports gates e
      (StableCSS.H_X (A := A) (B := B) (StableCSS.identityChecks (A := I) c.H_X))
      (StableCSS.H_X (A := A') (B := B') (StableCSS.identityChecks (A := I') d.H_X))
      (StableCSS.H_Z_dagger (A := A) (B := B) (dagger c.H_Z))
      (StableCSS.H_Z_dagger (A := A') (B := B') (dagger d.H_Z))) :
    Profile.S_X c ≅ Profile.S_X d :=
  stableCircuitProfileIso c.H_X d.H_X (dagger c.H_Z) (dagger d.H_Z) gates e h

end
end Decoupling.HighDim.ProfileStability
