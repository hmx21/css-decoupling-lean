import Decoupling.HighDim.DenseCircuitPermutationTheta
import Decoupling.HighDim.PhysicalIsomorphism

/-!
# Canonical physical species coordinates for the computed stabilization

The inner and outer Fin enumerations are explicit bijections. The source
and target physical ordinal labels are identified by the arithmetic cast,
not by silently applying a block swap. The actual compiler emits the needed
onsite SWAPs in these labels.
-/
namespace Decoupling.HighDim.AlgorithmTwoPhysicalTransport
open Matrix LaurentArithmetic Stabilization PhysicalIsomorphism
variable {K : Type*} [Field K] {D c0 c1 t0 t1 : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

abbrev Source (c0 c1 t0 t1 : ℕ) := (Fin c0 ⊕ Fin t1) ⊕ (Fin t0 ⊕ Fin c1)
abbrev Target (c0 c1 t0 t1 : ℕ) := (Fin t0 ⊕ Fin c1) ⊕ (Fin c0 ⊕ Fin t1)

def sourceCoordinates (c0 c1 t0 t1 : ℕ) : Source c0 c1 t0 t1 ≃ Fin ((c0+t1)+(t0+c1)) :=
  (Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv

def targetCoordinates (c0 c1 t0 t1 : ℕ) : Target c0 c1 t0 t1 ≃ Fin ((t0+c1)+(c0+t1)) :=
  (Equiv.sumCongr finSumFinEquiv finSumFinEquiv).trans finSumFinEquiv

/-- Identity of physical integer species labels, with only a type cast. -/
def ordinalIdentification (c0 c1 t0 t1 : ℕ) :
    Fin ((c0+t1)+(t0+c1)) ≃ Fin ((t0+c1)+(c0+t1)) :=
  finCongr (Nat.add_comm (c0+t1) (t0+c1))

@[simp] theorem ordinalIdentification_value (i : Fin ((c0+t1)+(t0+c1))) :
    (ordinalIdentification c0 c1 t0 t1 i).val = i.val := rfl

section Generic
variable {R : Type*} [CommRing R]
  {A B A' B' : Type*} [Fintype A] [Fintype B] [Fintype A'] [Fintype B']
  [DecidableEq A] [DecidableEq B] [DecidableEq A'] [DecidableEq B']

omit [Fintype B] [Fintype B'] in
/-- Reindexing the two rectangular maps reindexes the same signed theta. -/
theorem theta_reindex (f : Matrix B A R) (g : Matrix A B R) (a : A ≃ A') (b : B ≃ B') :
    theta (f.submatrix b.symm a.symm) (g.submatrix a.symm b.symm) =
      (theta f g).submatrix (Equiv.sumCongr b a).symm (Equiv.sumCongr a b).symm := by
  have hmul := Matrix.submatrix_mul_equiv f g b.symm a.symm b.symm
  ext i j
  rcases i with i|i <;> rcases j with j|j <;>
    simp [theta,Matrix.submatrix_apply,hmul,Matrix.one_apply]

end Generic

noncomputable section
variable (c : ComparisonData (Laurent K D) (Fin c0) (Fin c1) (Fin t0) (Fin t1))

def Uordinal : Matrix (Fin ((t0+c1)+(c0+t1))) (Fin ((c0+t1)+(t0+c1))) (Laurent K D) :=
  c.U.submatrix (targetCoordinates c0 c1 t0 t1).symm (sourceCoordinates c0 c1 t0 t1).symm

def UInvOrdinal : Matrix (Fin ((c0+t1)+(t0+c1))) (Fin ((t0+c1)+(c0+t1))) (Laurent K D) :=
  c.UInv.submatrix (sourceCoordinates c0 c1 t0 t1).symm (targetCoordinates c0 c1 t0 t1).symm

theorem Uordinal_inverse : Uordinal c * UInvOrdinal c = 1 := by
  rw [Uordinal,UInvOrdinal,Matrix.submatrix_mul_equiv,c.U_inverse.1,Matrix.submatrix_one_equiv]

variable {a b : ℕ}

/-- The real generated gate word acts by U in the stated canonical ordinals. -/
theorem actual_wordZ
    (psi : DenseMatrix K D (t0+c1) (c0+t1) a)
    (phi : DenseMatrix K D (c0+t1) (t0+c1) b)
    (hpsi : matrixDenote psi = c.psiHat.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
    (hphi : matrixDenote phi = c.phiHat.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) :
    Circuit.wordZ (DenseCircuitPermutation.canonicalThetaProgram psi phi).value =
      (Uordinal c).submatrix id (ordinalIdentification c0 c1 t0 t1).symm := by
  rw [DenseCircuitPermutation.canonicalThetaProgram_z,hpsi,hphi,theta_reindex]
  ext i j
  simp [Uordinal,ComparisonData.U,sourceCoordinates,targetCoordinates,
    ordinalIdentification,DenseCircuitPermutation.canonicalIdentification,Matrix.submatrix_apply]

/-- The X action of the same generated word is the inverse dagger, with no
characteristic-two sign simplification. -/
theorem actual_wordX
    (psi : DenseMatrix K D (t0+c1) (c0+t1) a)
    (phi : DenseMatrix K D (c0+t1) (t0+c1) b)
    (hpsi : matrixDenote psi = c.psiHat.submatrix finSumFinEquiv.symm finSumFinEquiv.symm)
    (hphi : matrixDenote phi = c.phiHat.submatrix finSumFinEquiv.symm finSumFinEquiv.symm) :
    Circuit.wordX (DenseCircuitPermutation.canonicalThetaProgram psi phi).value =
      dagger ((UInvOrdinal c).submatrix (ordinalIdentification c0 c1 t0 t1).symm id) := by
  apply Circuit.wordX_eq_dagger_inverse _ _ _ (actual_wordZ c psi phi hpsi hphi)
  rw [Matrix.submatrix_mul_equiv,Uordinal_inverse,Matrix.submatrix_id_id]

end
end Decoupling.HighDim.AlgorithmTwoPhysicalTransport
