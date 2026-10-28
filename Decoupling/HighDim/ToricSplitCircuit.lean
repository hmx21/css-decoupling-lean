import Decoupling.HighDim.ToricStackChecks
import Decoupling.HighDim.PhysicalIsomorphism

/-!
# Theorem 2, X-side: an actual split profile gives a same-lattice circuit

The input is an original topological CSS code and an isomorphism of its
native derived profile with the explicit split coefficient layers. The
output gives actual identity checks, product-state ancillary blocks,
and a finite word of physical SUM/SWAP layers transporting both actual
stabilizer modules. All comparison and model data are constructed.

The output lattice is unchanged. A finite index set lists individual
toric copies; the final specialization uses the paper's multiplicities
in forms `1,...,D-1`. Empty index sets and zero multiplicities are allowed.
-/

namespace Decoupling.HighDim.Toric

open CategoryTheory PhysicalIsomorphism

noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [Field K] (D : ℕ) {ι : Type} [Fintype ι] (forms : ι → ℕ)
  {q s r : ℕ}

/-- The explicit stable physical conclusion, without a supplied circuit
certificate. The two clauses of `Transports` concern Z and X generators. -/
def DecouplesToStack (c : CSS.Checks K D q s r) : Prop :=
  ∃ a b : ℕ, ∃ gates : List (Circuit.Layer K D
      ((Fin (stackCount D forms 1) ⊕ (Fin s ⊕ Fin a)) ⊕
        (Fin q ⊕ (Fin (stackCount D forms 0) ⊕ Fin b)))),
    Transports gates (Equiv.sumComm _ _)
      (StableCSS.H_X (A := Fin (stackCount D forms 0) ⊕ Fin b)
        (B := Fin (stackCount D forms 1) ⊕ (Fin s ⊕ Fin a))
        (StableCSS.identityChecks (A := Fin a) c.H_X))
      (StableCSS.H_X (A := Fin s ⊕ Fin a)
        (B := Fin q ⊕ (Fin (stackCount D forms 0) ⊕ Fin b))
        (StableCSS.identityChecks (A := Fin b) (stackChecks K D forms).H_X))
      (StableCSS.H_Z_dagger (A := Fin (stackCount D forms 0) ⊕ Fin b)
        (B := Fin (stackCount D forms 1) ⊕ (Fin s ⊕ Fin a)) (dagger c.H_Z))
      (StableCSS.H_Z_dagger (A := Fin s ⊕ Fin a)
        (B := Fin q ⊕ (Fin (stackCount D forms 0) ⊕ Fin b))
        (dagger (stackChecks K D forms).H_Z)) ∧
    LocalCircuit gates

/-- Same-lattice stable SUM/SWAP decoupling from the actual split profile.
Source topology remains the full two-sided condition. Target exactness
is proved from the actual Koszul complex, rather than assumed. -/
theorem decouples_of_split (c : CSS.Checks K D q s r) (hc : c.Topological)
    (e : Profile.S_X c ≅ splitTarget K D forms) : DecouplesToStack K D forms c := by
  classical
  obtain ⟨a, b, ⟨beta⟩⟩ := stableCheckCokernel_of_split K D forms c hc e
  obtain ⟨gates, htrans, _⟩ := exists_circuit_of_stableCheckEquiv
    c.H_X (stackChecks K D forms).H_X (dagger c.H_Z) (dagger (stackChecks K D forms).H_Z)
    (c.exact_X hc) (stackChecks_exact_X K D forms) beta (Equiv.sumComm _ _)
  exact ⟨a, b, gates, htrans, localCircuit gates⟩

/-- The actual finite index type of the paper's toric copies. -/
abbrev Copies (multiplicity : Fin (D - 1) → ℕ) := Σ j, Fin (multiplicity j)

def copyForms (multiplicity : Fin (D - 1) → ℕ) : Copies D multiplicity → ℕ :=
  fun copy => copy.1.val

/-- Theorem 2 in the exact permitted range of higher-form toric types.
An isomorphism of the genuine native profile is the theorem's advertised
premise; no hidden algebraic or circuit certificates occur. -/
theorem decouples_of_multiplicity_split (multiplicity : Fin (D - 1) → ℕ)
    (c : CSS.Checks K D q s r) (hc : c.Topological)
    (e : Profile.S_X c ≅ splitTarget K D (copyForms D multiplicity)) :
    DecouplesToStack K D (copyForms D multiplicity) c :=
  decouples_of_split K D (copyForms D multiplicity) c hc e

end
end Decoupling.HighDim.Toric
