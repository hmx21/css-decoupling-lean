import Decoupling.HighDim.AlgorithmTwoPhysicalTransport
import Decoupling.HighDim.ProductStates

/-!
# Actual ancillary coordinate blocks and their normalized product states

The counts are cardinalities of the very A and B summands in StableCSS,
not the total number of circuit species. Explicit generator formulas show
which identity X and Z factors were added. On every finite set of cells,
their full fixed spaces are the normalized |+> and |0> product-state lines.
-/
namespace Decoupling.HighDim.AlgorithmTwoPhysicalTransport
open Matrix LaurentArithmetic PhysicalIsomorphism
variable {K : Type*} [Field K] {D c0 c1 t0 t1 zc zt : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Number of actual source |+> qudits per unit cell. -/
def sourcePlusCount (t1 : ℕ) : ℕ := Fintype.card (Fin t1)
/-- Number of actual source |0> qudits per unit cell. -/
def sourceZeroCount (t0 c1 : ℕ) : ℕ := Fintype.card (Fin t0 ⊕ Fin c1)
def sourceAncillaCount (c1 t0 t1 : ℕ) : ℕ := sourcePlusCount t1+sourceZeroCount t0 c1
/-- Number of actual target |+> qudits per unit cell. -/
def targetPlusCount (c1 : ℕ) : ℕ := Fintype.card (Fin c1)
/-- Number of actual target |0> qudits per unit cell. -/
def targetZeroCount (c0 t1 : ℕ) : ℕ := Fintype.card (Fin c0 ⊕ Fin t1)
def targetAncillaCount (c0 c1 t1 : ℕ) : ℕ := targetPlusCount c1+targetZeroCount c0 t1

theorem actual_ancillary_ranks (c0 c1 t0 t1 : ℕ) :
    sourcePlusCount t1 = t1 ∧ sourceZeroCount t0 c1 = t0+c1 ∧
    targetPlusCount c1 = c1 ∧ targetZeroCount c0 t1 = c0+t1 ∧
    sourceAncillaCount c1 t0 t1 = t1+(t0+c1) ∧
    targetAncillaCount c0 c1 t1 = c1+(c0+t1) := by
  simp [sourcePlusCount,sourceZeroCount,targetPlusCount,targetZeroCount,sourceAncillaCount,targetAncillaCount]

theorem source_species_count (c0 c1 t0 t1 : ℕ) :
    Fintype.card (Source c0 c1 t0 t1) = c0+sourceAncillaCount c1 t0 t1 := by
  simp [Source,sourceAncillaCount,sourcePlusCount,sourceZeroCount,Nat.add_assoc]

theorem target_species_count (c0 c1 t0 t1 : ℕ) :
    Fintype.card (Target c0 c1 t0 t1) = t0+targetAncillaCount c0 c1 t1 := by
  simp [Target,targetAncillaCount,targetPlusCount,targetZeroCount,Nat.add_assoc]

noncomputable section

/-- All source X generators: original X support, arbitrary identity-X
support on the plus block, and zero on the zero-state block. -/
theorem source_X_generators (dC : Matrix (Fin c1) (Fin c0) (Laurent K D))
    (v : (Fin c1 ⊕ Fin t1) → Laurent K D) :
    dagger (sourceHX (t0 := t0) dC) *ᵥ v =
      (Sum.elim (Sum.elim (dagger dC *ᵥ (v ∘ Sum.inl)) (v ∘ Sum.inr)) 0) ∘
        (sourceCoordinates c0 c1 t0 t1).symm := by
  change (dagger (StableCSS.H_X (A := Fin t1) (B := Fin t0 ⊕ Fin c1) dC) *ᵥ v) ∘
      (sourceCoordinates c0 c1 t0 t1).symm = _
  rw [StableCSS.dagger_X_mulVec]

/-- All source Z generators: original Z support, zero on the plus block,
and arbitrary identity-Z support on the zero-state block. -/
theorem source_Z_generators (zC : Matrix (Fin c0) (Fin zc) (Laurent K D))
    (v : (Fin zc ⊕ (Fin t0 ⊕ Fin c1)) → Laurent K D) :
    sourceZ (t1 := t1) zC *ᵥ v =
      (Sum.elim (Sum.elim (zC *ᵥ (v ∘ Sum.inl)) 0) (v ∘ Sum.inr)) ∘
        (sourceCoordinates c0 c1 t0 t1).symm := by
  change (StableCSS.H_Z_dagger (A := Fin t1) (B := Fin t0 ⊕ Fin c1) zC *ᵥ v) ∘
      (sourceCoordinates c0 c1 t0 t1).symm = _
  rw [StableCSS.H_Z_dagger_mulVec]

theorem target_X_generators (dT : Matrix (Fin t1) (Fin t0) (Laurent K D))
    (v : (Fin t1 ⊕ Fin c1) → Laurent K D) :
    dagger (targetHX (c0 := c0) dT) *ᵥ v =
      (Sum.elim (Sum.elim (dagger dT *ᵥ (v ∘ Sum.inl)) (v ∘ Sum.inr)) 0) ∘
        (targetCoordinates c0 c1 t0 t1).symm := source_X_generators dT v

theorem target_Z_generators (zT : Matrix (Fin t0) (Fin zt) (Laurent K D))
    (v : (Fin zt ⊕ (Fin c0 ⊕ Fin t1)) → Laurent K D) :
    targetZ (c1 := c1) zT *ᵥ v =
      (Sum.elim (Sum.elim (zT *ᵥ (v ∘ Sum.inl)) 0) (v ∘ Sum.inr)) ∘
        (targetCoordinates c0 c1 t0 t1).symm := source_Z_generators zT v

/-- The actual finite Hilbert-space semantics of one pair of ancillary
blocks. The states, their complete fixed spaces and norms are specified. -/
structure ProductAncillaSemantics (p : ℕ) [NeZero p]
    (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] : Prop where
  plus_fixed : (PauliUnitary.fixedX : Submodule ℂ (PauliUnitary.State p A)) =
    Submodule.span ℂ {PauliUnitary.plusState}
  zero_fixed : (PauliUnitary.fixedZ : Submodule ℂ (PauliUnitary.State p B)) =
    Submodule.span ℂ {PauliUnitary.zeroState}
  plus_normalized : ‖WithLp.toLp 2 (PauliUnitary.plusState (p := p) (ι := A))‖ = 1
  zero_normalized : ‖WithLp.toLp 2 (PauliUnitary.zeroState (p := p) (ι := B))‖ = 1
  plus_dimension : Module.finrank ℂ (PauliUnitary.fixedX (p := p) (ι := A)) = 1
  zero_dimension : Module.finrank ℂ (PauliUnitary.fixedZ (p := p) (ι := B)) = 1

theorem productAncillaSemantics (p : ℕ) [NeZero p]
    (A B : Type*) [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] :
    ProductAncillaSemantics p A B :=
  ⟨PauliUnitary.fixedX_eq_span,PauliUnitary.fixedZ_eq_span,
    PauliUnitary.plusState_norm,PauliUnitary.zeroState_norm,
    PauliUnitary.fixedX_finrank,PauliUnitary.fixedZ_finrank⟩

/-- Every finite cell window has the actual source and target product-state
ancillas attached to the matrix blocks above. Empty windows are included. -/
theorem ancillary_states (p c0 c1 t0 t1 : ℕ) [Fact p.Prime]
    (Cells : Type*) [Fintype Cells] [DecidableEq Cells] :
    ProductAncillaSemantics p (Fin t1 × Cells) ((Fin t0 ⊕ Fin c1) × Cells) ∧
    ProductAncillaSemantics p (Fin c1 × Cells) ((Fin c0 ⊕ Fin t1) × Cells) :=
  ⟨productAncillaSemantics _ _ _,productAncillaSemantics _ _ _⟩

end
end Decoupling.HighDim.AlgorithmTwoPhysicalTransport
