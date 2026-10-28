import Decoupling.HighDim.AlgorithmTwoPhysicalTransportCoordinates

/-!
# The actual computed ordinal gate word transports both stabilizer modules

The gates are the materialized canonicalThetaProgram psiHat phiHat output.
The proof uses the U,V square of that same comparison datum, not a newly
selected circuit. Both stabilizer image equalities are stated for the
literal product-state stabilization in canonical physical Fin coordinates.
-/
namespace Decoupling.HighDim.AlgorithmTwoPhysicalTransport
open Matrix LaurentArithmetic Stabilization PhysicalIsomorphism
variable {K : Type*} [Field K] {D c0 c1 t0 t1 zc zt : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section

section Reindex
variable {Q Q' C Z : Type*} [Fintype Q] [Fintype Q'] [Fintype Z]

/-- A genuine species coordinate bijection preserves the complete kernel/image equality. -/
theorem exactness_reindex (H : Matrix C Q (Laurent K D)) (B : Matrix Q Z (Laurent K D))
    (e : Q ≃ Q') (h : ∀ v, H *ᵥ v = 0 ↔ inImage B v) (v : Q' → Laurent K D) :
    H.submatrix id e.symm *ᵥ v = 0 ↔ inImage (B.submatrix e.symm id) v := by
  rw [Matrix.submatrix_mulVec_equiv]
  change H *ᵥ (v ∘ e) = 0 ↔ _
  rw [h]
  constructor
  · rintro ⟨z,hz⟩
    refine ⟨z,?_⟩
    funext i
    have hi := congrFun hz (e.symm i)
    simpa only [Matrix.mulVec,Matrix.submatrix_apply,id_eq,Function.comp_apply,Equiv.apply_symm_apply] using hi
  · rintro ⟨z,hz⟩
    refine ⟨z,?_⟩
    funext i
    have hi := congrFun hz (e i)
    simpa only [Matrix.mulVec,Matrix.submatrix_apply,Equiv.symm_apply_apply,Function.comp_apply,id_eq] using hi

end Reindex

def sourceHX (dC : Matrix (Fin c1) (Fin c0) (Laurent K D)) :
    Matrix (Fin c1 ⊕ Fin t1) (Fin ((c0+t1)+(t0+c1))) (Laurent K D) :=
  (StableCSS.H_X (A := Fin t1) (B := Fin t0 ⊕ Fin c1) dC).submatrix id
    (sourceCoordinates c0 c1 t0 t1).symm

def targetHX (dT : Matrix (Fin t1) (Fin t0) (Laurent K D)) :
    Matrix (Fin t1 ⊕ Fin c1) (Fin ((t0+c1)+(c0+t1))) (Laurent K D) :=
  (StableCSS.H_X (A := Fin c1) (B := Fin c0 ⊕ Fin t1) dT).submatrix id
    (targetCoordinates c0 c1 t0 t1).symm

def sourceZ (zC : Matrix (Fin c0) (Fin zc) (Laurent K D)) :
    Matrix (Fin ((c0+t1)+(t0+c1))) (Fin zc ⊕ (Fin t0 ⊕ Fin c1)) (Laurent K D) :=
  (StableCSS.H_Z_dagger (A := Fin t1) (B := Fin t0 ⊕ Fin c1) zC).submatrix
    (sourceCoordinates c0 c1 t0 t1).symm id

def targetZ (zT : Matrix (Fin t0) (Fin zt) (Laurent K D)) :
    Matrix (Fin ((t0+c1)+(c0+t1))) (Fin zt ⊕ (Fin c0 ⊕ Fin t1)) (Laurent K D) :=
  (StableCSS.H_Z_dagger (A := Fin c1) (B := Fin c0 ⊕ Fin t1) zT).submatrix
    (targetCoordinates c0 c1 t0 t1).symm id

variable (c : ComparisonData (Laurent K D) (Fin c0) (Fin c1) (Fin t0) (Fin t1))

theorem square_ordinal : targetHX (c0 := c0) c.dT * Uordinal c =
    c.V * sourceHX (t0 := t0) c.dC := by
  change c.dTHat.submatrix id (targetCoordinates c0 c1 t0 t1).symm *
    c.U.submatrix (targetCoordinates c0 c1 t0 t1).symm (sourceCoordinates c0 c1 t0 t1).symm =
      c.V * c.dCHat.submatrix id (sourceCoordinates c0 c1 t0 t1).symm
  rw [Matrix.submatrix_mul_equiv,c.stabilized_square]
  exact Matrix.submatrix_mul c.V c.dCHat id id _ Function.bijective_id

variable {a b : ℕ}

/-- Both literal stabilized stabilizer modules are transported by the same
actual returned canonical SUM/SWAP word. No gate list is an input. -/
theorem transports
    (zC : Matrix (Fin c0) (Fin zc) (Laurent K D)) (zT : Matrix (Fin t0) (Fin zt) (Laurent K D))
    (hC : ∀ v, c.dC *ᵥ v = 0 ↔ inImage zC v)
    (hT : ∀ v, c.dT *ᵥ v = 0 ↔ inImage zT v)
    (psi : DenseMatrix K D (t0+c1) (c0+t1) a)
    (phi : DenseMatrix K D (c0+t1) (t0+c1) b)
    (hpsi : matrixDenote psi = c.psiHat.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
    (hphi : matrixDenote phi = c.phiHat.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) :
    Transports (DenseCircuitPermutation.canonicalThetaProgram psi phi).value
      (ordinalIdentification c0 c1 t0 t1) (sourceHX c.dC) (targetHX c.dT) (sourceZ zC) (targetZ zT) := by
  apply transports_of_actions _ _ _ _ _ _ (Uordinal c) (UInvOrdinal c) c.V c.VInv
    (Uordinal_inverse c) c.V_inverse.2 (square_ordinal c)
  · exact exactness_reindex _ _ (sourceCoordinates c0 c1 t0 t1)
      (StableCSS.exactness c.dC zC hC)
  · exact exactness_reindex _ _ (targetCoordinates c0 c1 t0 t1)
      (StableCSS.exactness c.dT zT hT)
  · exact actual_wordZ c psi phi hpsi hphi
  · exact actual_wordX c psi phi hpsi hphi

/-- Locality is proved for the materialized gate word: disjoint physical
pairs, bounded range, finite depth and translation covariance in each layer. -/
theorem actual_localCircuit
    (psi : DenseMatrix K D (t0+c1) (c0+t1) a)
    (phi : DenseMatrix K D (c0+t1) (t0+c1) b) :
    LocalCircuit (DenseCircuitPermutation.canonicalThetaProgram psi phi).value := localCircuit _

/-- The reverse topological equality is also preserved, independently of
the transport proof that uses the forward kernel/image equality. -/
theorem stabilized_topological
    (zC : Matrix (Fin c0) (Fin zc) (Laurent K D)) (zT : Matrix (Fin t0) (Fin zt) (Laurent K D))
    (hCX : ∀ v, c.dC *ᵥ v = 0 ↔ inImage zC v)
    (hCZ : ∀ v, dagger zC *ᵥ v = 0 ↔ inImage (dagger c.dC) v)
    (hTX : ∀ v, c.dT *ᵥ v = 0 ↔ inImage zT v)
    (hTZ : ∀ v, dagger zT *ᵥ v = 0 ↔ inImage (dagger c.dT) v) :
    (∀ v, sourceHX (t0 := t0) (t1 := t1) c.dC *ᵥ v = 0 ↔ inImage (sourceZ zC) v) ∧
    (∀ v, dagger (sourceZ (c1 := c1) (t0 := t0) (t1 := t1) zC) *ᵥ v = 0 ↔
      inImage (dagger (sourceHX c.dC)) v) ∧
    (∀ v, targetHX (c0 := c0) (c1 := c1) c.dT *ᵥ v = 0 ↔ inImage (targetZ zT) v) ∧
    (∀ v, dagger (targetZ (c0 := c0) (c1 := c1) (t1 := t1) zT) *ᵥ v = 0 ↔
      inImage (dagger (targetHX c.dT)) v) := by
  refine ⟨?_,?_,?_,?_⟩
  · exact exactness_reindex _ _ (sourceCoordinates c0 c1 t0 t1) (StableCSS.exactness _ _ hCX)
  · exact exactness_reindex
      (dagger (StableCSS.H_Z_dagger (A := Fin t1) (B := Fin t0 ⊕ Fin c1) zC))
      (dagger (StableCSS.H_X (A := Fin t1) (B := Fin t0 ⊕ Fin c1) c.dC))
      (sourceCoordinates c0 c1 t0 t1)
      (StableCSS.reverse_exactness (A := Fin t1) (B := Fin t0 ⊕ Fin c1) c.dC zC hCZ)
  · exact exactness_reindex _ _ (targetCoordinates c0 c1 t0 t1) (StableCSS.exactness _ _ hTX)
  · exact exactness_reindex
      (dagger (StableCSS.H_Z_dagger (A := Fin c1) (B := Fin c0 ⊕ Fin t1) zT))
      (dagger (StableCSS.H_X (A := Fin c1) (B := Fin c0 ⊕ Fin t1) c.dT))
      (targetCoordinates c0 c1 t0 t1)
      (StableCSS.reverse_exactness (A := Fin c1) (B := Fin c0 ⊕ Fin t1) c.dT zT hTZ)

end
end Decoupling.HighDim.AlgorithmTwoPhysicalTransport
