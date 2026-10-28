import Decoupling.HighDim.AlgorithmTwoPhysicalTransportAncillas

/-!
# Physical realization of the actual computed word

Every layer is a genuine local complex unitary on its physical pair, with
exact X and Z conjugation compatible with the infinite-lattice Laurent
labels. Together with disjointness and translation covariance this is the
same finite-support Pauli semantics used by the baseline physical theorem;
no undefined infinite tensor product is introduced here.
-/
namespace Decoupling.HighDim.AlgorithmTwoPhysicalTransport
open Matrix LaurentArithmetic Stabilization PhysicalIsomorphism
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

variable {p D : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact local Hilbert-space semantics of every actual gate in the list. -/
def LocalPauliSemantics (gates : List (Circuit.Layer (ZMod p) D ι)) : Prop :=
  ∀ g ∈ gates, ∀ n : Translation D, ∀ v : ι → Laurent (ZMod p) D,
    (((PauliUnitary.layerLocalUnitary g : Matrix (PauliUnitary.Config p Bool) _ ℂ) *
      PauliUnitary.X (PauliUnitary.layerPairRestriction g n (fun i => (v i).coeff))) *
      (PauliUnitary.layerLocalUnitary g : Matrix (PauliUnitary.Config p Bool) _ ℂ)ᴴ =
        PauliUnitary.X (PauliUnitary.layerPairRestriction g n (fun i => ((g.xMatrix *ᵥ v) i).coeff))) ∧
    (((PauliUnitary.layerLocalUnitary g : Matrix (PauliUnitary.Config p Bool) _ ℂ) *
      PauliUnitary.Z (PauliUnitary.layerPairRestriction g n (fun i => (v i).coeff))) *
      (PauliUnitary.layerLocalUnitary g : Matrix (PauliUnitary.Config p Bool) _ ℂ)ᴴ =
        PauliUnitary.Z (PauliUnitary.layerPairRestriction g n (fun i => ((g.zMatrix *ᵥ v) i).coeff)))

theorem localPauliSemantics (gates : List (Circuit.Layer (ZMod p) D ι)) : LocalPauliSemantics gates := by
  intro g _ n v
  exact ⟨PauliUnitary.layerLocal_X_compatible g n v,PauliUnitary.layerLocal_Z_compatible g n v⟩

variable {c0 c1 t0 t1 zc zt a b : ℕ}

/-- One actual returned word, both stabilizer transports, all local quantum
semantics, normalized product-state ancillary factors, and its actual depth
bound. The source/target ancilla counts are the block cardinalities proved
in actual_ancillary_ranks, rather than the total circuit width. -/
theorem physical_realization
    (c : ComparisonData (Laurent (ZMod p) D) (Fin c0) (Fin c1) (Fin t0) (Fin t1))
    (zC : Matrix (Fin c0) (Fin zc) (Laurent (ZMod p) D))
    (zT : Matrix (Fin t0) (Fin zt) (Laurent (ZMod p) D))
    (hC : ∀ v, c.dC *ᵥ v = 0 ↔ inImage zC v)
    (hT : ∀ v, c.dT *ᵥ v = 0 ↔ inImage zT v)
    (psi : DenseMatrix (ZMod p) D (t0+c1) (c0+t1) a)
    (phi : DenseMatrix (ZMod p) D (c0+t1) (t0+c1) b)
    (hpsi : matrixDenote psi = c.psiHat.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
    (hphi : matrixDenote phi = c.phiHat.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
    (Cells : Type*) [Fintype Cells] [DecidableEq Cells] :
    let gates := (DenseCircuitPermutation.canonicalThetaProgram psi phi).value
    Transports gates (ordinalIdentification c0 c1 t0 t1)
      (sourceHX c.dC) (targetHX c.dT) (sourceZ zC) (targetZ zT) ∧
    LocalCircuit gates ∧ LocalPauliSemantics gates ∧
    ProductAncillaSemantics p (Fin t1 × Cells) ((Fin t0 ⊕ Fin c1) × Cells) ∧
    ProductAncillaSemantics p (Fin c1 × Cells) ((Fin c0 ⊕ Fin t1) × Cells) ∧
    gates.length ≤ (t0+c1)*(c0+t1)*boxSize D a +
      (c0+t1)*(t0+c1)*boxSize D b+(t0+c1)+(c0+t1) := by
  exact ⟨transports c zC zT hC hT psi phi hpsi hphi,
    actual_localCircuit psi phi,localPauliSemantics _,
    (ancillary_states p c0 c1 t0 t1 Cells).1,(ancillary_states p c0 c1 t0 t1 Cells).2,
    DenseCircuitPermutation.canonicalThetaProgram_length psi phi⟩

end
end Decoupling.HighDim.AlgorithmTwoPhysicalTransport
