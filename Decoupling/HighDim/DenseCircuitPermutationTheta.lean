import Decoupling.HighDim.DenseCircuitPermutationRelabel

/-!
# Theta words with real onsite permutations and canonical Fin species

All required permutations are emitted as SWAP gates. The canonical
wrapper uses the same physical Fin(n+m) label on input and output;
its array-order identification is explicit and no block swap is free.
-/
namespace Decoupling.HighDim.DenseCircuitPermutation
open Circuit LaurentArithmetic ArithmeticCost Matrix
variable {K : Type*} [Field K] {D m n a b : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def thetaProgramWith (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b)
    (e : (Fin m ⊕ Fin n) ≃ (Fin n ⊕ Fin m)) : Work K (List (Circuit.Layer K D (Fin n ⊕ Fin m))) :=
  Work.bind (DenseShearCompile.thetaProgram f g) fun word =>
    Work.pure (word ++ (compileSum n m (e.symm.trans (Equiv.sumComm _ _))).map Circuit.Layer.swap)

theorem thetaProgramWith_cost (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b)
    (e : (Fin m ⊕ Fin n) ≃ (Fin n ⊕ Fin m)) :
    (thetaProgramWith f g e).cost = n*m*boxSize D a + 2*(m*n*boxSize D b) := by
  simp [thetaProgramWith]

theorem thetaProgramWith_length (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b)
    (e : (Fin m ⊕ Fin n) ≃ (Fin n ⊕ Fin m)) :
    (thetaProgramWith f g e).value.length ≤ n*m*boxSize D a + m*n*boxSize D b + n+m := by
  simp only [thetaProgramWith, Work.bind_value, Work.pure_value, List.length_append,
    List.length_map, DenseShearCompile.thetaProgram_length]
  have hp := compileSum_length n m (e.symm.trans (Equiv.sumComm _ _))
  omega

private theorem theta_shear_z (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    Circuit.wordZ (DenseShearCompile.thetaProgram f g).value =
      Circuit.upper (matrixDenote f) * Circuit.lower (-matrixDenote g) := by
  simp only [DenseShearCompile.thetaProgram, Work.bind_value, Work.pure_value, Circuit.wordZ_sum]
  rw [DenseShearCompile.twoShearProgram_action, matrixNegProgram_correct]

theorem thetaProgramWith_z (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b)
    (e : (Fin m ⊕ Fin n) ≃ (Fin n ⊕ Fin m)) :
    Circuit.wordZ (thetaProgramWith f g e).value =
      (Stabilization.theta (matrixDenote f) (matrixDenote g)).submatrix id e.symm := by
  rw [thetaProgramWith, Work.bind_value, Work.pure_value, Circuit.wordZ_append,
    theta_shear_z, Circuit.wordZ_swap, compileSum_action, Circuit.theta_reindexed]

theorem thetaProgramWith_x (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b)
    (e : (Fin m ⊕ Fin n) ≃ (Fin n ⊕ Fin m)) :
    Circuit.wordX (thetaProgramWith f g e).value =
      dagger ((Stabilization.theta (matrixDenote g) (matrixDenote f)).submatrix e.symm id) := by
  apply Circuit.wordX_eq_dagger_inverse _ _ _ (thetaProgramWith_z f g e)
  rw [Matrix.submatrix_mul_equiv, Stabilization.theta_mul_reverse, Matrix.submatrix_id_id]

/-- Identity of physical ordinal labels, with the natural arithmetic
cast between the two equal total sizes. This is not the block swap. -/
def canonicalIdentification (m n : ℕ) : (Fin m ⊕ Fin n) ≃ (Fin n ⊕ Fin m) :=
  finSumFinEquiv.trans ((finCongr (Nat.add_comm m n)).trans finSumFinEquiv.symm)

theorem canonicalIdentification_index (m n : ℕ) (i : Fin m ⊕ Fin n) :
    (finSumFinEquiv (canonicalIdentification m n i)).val = (finSumFinEquiv i).val := by
  simp [canonicalIdentification]

def canonicalThetaProgram (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    Work K (List (Circuit.Layer K D (Fin (n+m)))) :=
  Work.bind (thetaProgramWith f g (canonicalIdentification m n)) fun word =>
    Work.pure (word.map (relabelLayer finSumFinEquiv))

theorem canonicalThetaProgram_cost (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    (canonicalThetaProgram f g).cost = n*m*boxSize D a + 2*(m*n*boxSize D b) := by
  simp [canonicalThetaProgram, thetaProgramWith_cost]

theorem canonicalThetaProgram_length (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    (canonicalThetaProgram f g).value.length ≤ n*m*boxSize D a + m*n*boxSize D b + n+m := by
  simpa only [canonicalThetaProgram, Work.bind_value, Work.pure_value, List.length_map] using
    thetaProgramWith_length f g (canonicalIdentification m n)

theorem canonicalThetaProgram_z (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    Circuit.wordZ (canonicalThetaProgram f g).value =
      ((Stabilization.theta (matrixDenote f) (matrixDenote g)).submatrix id
        (canonicalIdentification m n).symm).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := by
  rw [canonicalThetaProgram, Work.bind_value, Work.pure_value, relabel_wordZ, thetaProgramWith_z]

theorem canonicalThetaProgram_x (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    Circuit.wordX (canonicalThetaProgram f g).value =
      dagger (((Stabilization.theta (matrixDenote g) (matrixDenote f)).submatrix
        (canonicalIdentification m n).symm id).submatrix finSumFinEquiv.symm finSumFinEquiv.symm) := by
  apply Circuit.wordX_eq_dagger_inverse _ _ _ (canonicalThetaProgram_z f g)
  rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
    Stabilization.theta_mul_reverse, Matrix.submatrix_id_id, Matrix.submatrix_one_equiv]

end Decoupling.HighDim.DenseCircuitPermutation
