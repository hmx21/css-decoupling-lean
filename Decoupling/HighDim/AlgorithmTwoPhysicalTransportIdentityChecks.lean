import Decoupling.HighDim.AlgorithmTwoPhysicalTransportRealization

/-!
# Original checks with the computed C4 identity-check rows

The extra C4 rows are identity-valued checks, not physical ancillas. Their
actual kernel and X-stabilizer image are unchanged. The subsequent plus/zero
ancillas are exactly the StableCSS blocks with these enlarged check ranks.
-/
namespace Decoupling.HighDim.AlgorithmTwoPhysicalTransport
open Matrix LaurentArithmetic Stabilization PhysicalIsomorphism
variable {K : Type*} [Field K] {D c0 c1 t0 t1 zc zt extraC extraT a b : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

/-- Literal zero-row insertion in the same Fin order used by the dense C4 output. -/
def identityChecksOrdinal (d : Matrix (Fin c1) (Fin c0) (Laurent K D)) (extra : ℕ) :
    Matrix (Fin (c1+extra)) (Fin c0) (Laurent K D) :=
  (StableCSS.identityChecks (A := Fin extra) d).submatrix finSumFinEquiv.symm id

theorem identityChecksOrdinal_kernel (d : Matrix (Fin c1) (Fin c0) (Laurent K D)) (extra : ℕ)
    (v : Fin c0 → Laurent K D) : identityChecksOrdinal d extra *ᵥ v = 0 ↔ d *ᵥ v = 0 := by
  have he : identityChecksOrdinal d extra *ᵥ v =
      (StableCSS.identityChecks (A := Fin extra) d *ᵥ v) ∘ finSumFinEquiv.symm := rfl
  rw [he]
  constructor
  · intro h
    apply (StableCSS.identityChecks_kernel (A := Fin extra) d v).mp
    funext i
    simpa only [Function.comp_apply,Equiv.symm_apply_apply,Pi.zero_apply] using
      congrFun h (finSumFinEquiv i)
  · intro h
    rw [(StableCSS.identityChecks_kernel (A := Fin extra) d v).mpr h]
    rfl

theorem identityChecksOrdinal_X_image (d : Matrix (Fin c1) (Fin c0) (Laurent K D)) (extra : ℕ)
    (v : Fin c0 → Laurent K D) :
    inImage (dagger (identityChecksOrdinal d extra)) v ↔ inImage (dagger d) v := by
  constructor
  · rintro ⟨z,hz⟩
    apply (StableCSS.identityChecks_dagger_image (I := Fin extra) d v).mp
    refine ⟨z ∘ finSumFinEquiv,?_⟩
    change (dagger (StableCSS.identityChecks (A := Fin extra) d)).submatrix id finSumFinEquiv.symm *ᵥ z = v at hz
    rw [Matrix.submatrix_mulVec_equiv] at hz
    exact hz
  · intro h
    obtain ⟨z,hz⟩ := (StableCSS.identityChecks_dagger_image (I := Fin extra) d v).mpr h
    refine ⟨z ∘ finSumFinEquiv.symm,?_⟩
    change (dagger (StableCSS.identityChecks (A := Fin extra) d)).submatrix id finSumFinEquiv.symm *ᵥ
      (z ∘ finSumFinEquiv.symm) = v
    rw [Matrix.submatrix_mulVec_equiv]
    simpa only [Function.comp_def,Equiv.symm_symm,Equiv.symm_apply_apply,id_eq] using hz

/-- Both original topological equalities survive exactly the computed
identity-check insertion. -/
theorem identityChecksOrdinal_topological
    (d : Matrix (Fin c1) (Fin c0) (Laurent K D)) (z : Matrix (Fin c0) (Fin zc) (Laurent K D))
    (extra : ℕ) (hX : ∀ v, d *ᵥ v = 0 ↔ inImage z v)
    (hZ : ∀ v, dagger z *ᵥ v = 0 ↔ inImage (dagger d) v) :
    (∀ v, identityChecksOrdinal d extra *ᵥ v = 0 ↔ inImage z v) ∧
    (∀ v, dagger z *ᵥ v = 0 ↔ inImage (dagger (identityChecksOrdinal d extra)) v) :=
  ⟨fun v => (identityChecksOrdinal_kernel d extra v).trans (hX v),
    fun v => (hZ v).trans (identityChecksOrdinal_X_image d extra v).symm⟩

/-- Actual generated word transport from original physical checks, after
precisely the C4 identity-check insertion and the specified product ancillas. -/
theorem transports_original_checks
    (dC : Matrix (Fin c1) (Fin c0) (Laurent K D))
    (dT : Matrix (Fin t1) (Fin t0) (Laurent K D))
    (zC : Matrix (Fin c0) (Fin zc) (Laurent K D))
    (zT : Matrix (Fin t0) (Fin zt) (Laurent K D))
    (hC : ∀ v, dC *ᵥ v = 0 ↔ inImage zC v)
    (hT : ∀ v, dT *ᵥ v = 0 ↔ inImage zT v)
    (c : ComparisonData (Laurent K D) (Fin c0) (Fin (c1+extraC)) (Fin t0) (Fin (t1+extraT)))
    (hdC : c.dC = identityChecksOrdinal dC extraC)
    (hdT : c.dT = identityChecksOrdinal dT extraT)
    (psi : DenseMatrix K D (t0+(c1+extraC)) (c0+(t1+extraT)) a)
    (phi : DenseMatrix K D (c0+(t1+extraT)) (t0+(c1+extraC)) b)
    (hpsi : matrixDenote psi = c.psiHat.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
    (hphi : matrixDenote phi = c.phiHat.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) :
    Transports (DenseCircuitPermutation.canonicalThetaProgram psi phi).value
      (ordinalIdentification c0 (c1+extraC) t0 (t1+extraT))
      (sourceHX (identityChecksOrdinal dC extraC)) (targetHX (identityChecksOrdinal dT extraT))
      (sourceZ zC) (targetZ zT) ∧
    LocalCircuit (DenseCircuitPermutation.canonicalThetaProgram psi phi).value := by
  refine ⟨?_,actual_localCircuit psi phi⟩
  rw [←hdC,←hdT]
  apply transports c zC zT _ _ psi phi hpsi hphi
  · intro v
    rw [hdC]
    exact (identityChecksOrdinal_kernel dC extraC v).trans (hC v)
  · intro v
    rw [hdT]
    exact (identityChecksOrdinal_kernel dT extraT v).trans (hT v)

/-- Substituting the C4 free check ranks gives the actual added physical
qudit counts; the identity-check rows are not counted again as qudits. -/
theorem ancillary_ranks_with_identity_checks (c0 c1 t0 t1 extraC extraT : ℕ) :
    sourceAncillaCount (c1+extraC) t0 (t1+extraT) = (t1+extraT)+(t0+(c1+extraC)) ∧
    targetAncillaCount c0 (c1+extraC) (t1+extraT) = (c1+extraC)+(c0+(t1+extraT)) := by
  simp [sourceAncillaCount,sourcePlusCount,sourceZeroCount,
    targetAncillaCount,targetPlusCount,targetZeroCount]

end
end Decoupling.HighDim.AlgorithmTwoPhysicalTransport
