import Decoupling.HighDim.GluedSplit
import Decoupling.HighDim.ShearCompile

/-! The explicit nullhomotopy gives invertible finite coarse-cell matrices. -/

namespace Decoupling.HighDim.GluedDirectional

open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (p : ℕ) [Fact p.Prime]

def quditMatrix : Matrix (Fin 6 × Fin p) (Fin 6 × Fin p) (Laurent (ZMod p) 3) :=
  1 + operatorMatrix p (quditN p)

def quditInverse : Matrix (Fin 6 × Fin p) (Fin 6 × Fin p) (Laurent (ZMod p) 3) :=
  1 - operatorMatrix p (quditN p)

def syndromeMatrix : Matrix (Fin 4 × Fin p) (Fin 4 × Fin p) (Laurent (ZMod p) 3) :=
  1 + operatorMatrix p (syndromeN p)

def syndromeInverse : Matrix (Fin 4 × Fin p) (Fin 4 × Fin p) (Laurent (ZMod p) 3) :=
  1 - operatorMatrix p (syndromeN p)

theorem qudit_inverse : quditMatrix p * quditInverse p = 1 := by
  have h : operatorMatrix p (quditN p) * operatorMatrix p (quditN p) = 0 := by
    rw [← operatorMatrix_comp, quditN_squared, operatorMatrix_zero]
  simp [quditMatrix, quditInverse, Matrix.add_mul, Matrix.mul_sub, h]

theorem syndrome_inverse : syndromeInverse p * syndromeMatrix p = 1 := by
  have h : operatorMatrix p (syndromeN p) * operatorMatrix p (syndromeN p) = 0 := by
    rw [← operatorMatrix_comp, syndromeN_squared, operatorMatrix_zero]
  simp [syndromeMatrix, syndromeInverse, Matrix.sub_mul, Matrix.mul_add, h]

theorem matrix_square : expandMatrix p (Glued.splitX (ZMod p)) * quditMatrix p =
    syndromeMatrix p * expandMatrix p (Glued.xChecks (ZMod p)) := by
  have h := congrArg (operatorMatrix p) (split_square p)
  simpa only [operatorMatrix_comp, operatorMatrix_add, operatorMatrix_id,
    quditMatrix, syndromeMatrix, expandMatrix] using h

theorem quditN_entry (i j : Fin 6) (r t : Fin p) :
    operatorMatrix p (quditN p) (i, r) (j, t) =
      if (i = 1 ∧ j = 3) ∨ (i = 2 ∧ j = 4) then
        rowCoordinates p (laurentDerivative (ZMod p) 1 (monomial (ZMod p) (row p t))) r
      else 0 := by
  rw [operatorMatrix, LinearMap.toMatrix'_apply]
  change vectorCoordinates p 6
    (quditN p ((vectorCoordinates p 6).symm (Pi.single (j, t) 1))) (i, r) = _
  rw [vectorCoordinates_symm_single]
  fin_cases i <;> fin_cases j <;>
    simp [quditN, vectorCoordinates]

def blockSpecies : ((Fin 3 × Fin p) ⊕ (Fin 3 × Fin p)) ≃ (Fin 6 × Fin p) :=
  (Equiv.sumProdDistrib (Fin 3) (Fin 3) (Fin p)).symm.trans
    (Equiv.prodCongr finSumFinEquiv (Equiv.refl (Fin p)))

def shearBlock : Matrix (Fin 3 × Fin p) (Fin 3 × Fin p) (Laurent (ZMod p) 3) :=
  fun i j => operatorMatrix p (quditN p) (blockSpecies p (Sum.inl i))
    (blockSpecies p (Sum.inr j))

/-- The change is an actual unitriangular shear on the original two blocks. -/
theorem quditMatrix_upper : quditMatrix p =
    (Circuit.upper (shearBlock p)).submatrix (blockSpecies p).symm (blockSpecies p).symm := by
  apply Matrix.ext
  intro i j
  obtain ⟨i, rfl⟩ := (blockSpecies p).surjective i
  obtain ⟨j, rfl⟩ := (blockSpecies p).surjective j
  simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  cases i with
  | inl i =>
    cases j with
    | inl j =>
      rcases i with ⟨i, r⟩
      rcases j with ⟨j, t⟩
      fin_cases i <;> fin_cases j <;>
        simp [quditMatrix, Circuit.upper, blockSpecies, quditN_entry, finSumFinEquiv,
          Matrix.one_apply, Prod.ext_iff]
    | inr j =>
      rcases i with ⟨i, r⟩
      rcases j with ⟨j, t⟩
      fin_cases i <;> fin_cases j <;>
        simp [quditMatrix, Circuit.upper, shearBlock, blockSpecies]
  | inr i =>
    cases j with
    | inl j =>
      rcases i with ⟨i, r⟩
      rcases j with ⟨j, t⟩
      fin_cases i <;> fin_cases j <;>
        simp [quditMatrix, Circuit.upper, blockSpecies, quditN_entry, finSumFinEquiv]
    | inr j =>
      rcases i with ⟨i, r⟩
      rcases j with ⟨j, t⟩
      fin_cases i <;> fin_cases j <;>
        simp [quditMatrix, Circuit.upper, blockSpecies, quditN_entry, finSumFinEquiv,
          Matrix.one_apply, Prod.ext_iff]

end
end Decoupling.HighDim.GluedDirectional
