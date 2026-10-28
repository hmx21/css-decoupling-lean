import Decoupling.HighDim.Onsite
import Decoupling.HighDim.Stabilization

/-!
# Finite SUM/SWAP realization of the signed stabilization matrix

Source: `drafts/main.tex`, Sections IV.B--C. The source and target of
`Θ(f,g)` have opposite summand orders. An explicit species equivalence
identifies them for execution. The theorem compiles both signed shears
and the remaining on-site permutation into actual SUM/SWAP layers, and
proves both the Z action and its required inverse-dagger X action.

The result concerns the finite-support label semantics established in
`Circuit` and `Onsite`. It does not by itself assert the existence of
comparison data, the split profile theorem, or complex Hilbert semantics.
-/

noncomputable section

namespace Decoupling.HighDim.Circuit

open Matrix

variable {K : Type*} [CommRing K] {D : ℕ}
variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

def blockPermutation : Matrix (V ⊕ U) (U ⊕ V) (Laurent K D) :=
  fromBlocks 0 1 1 0

omit [Fintype U] [Fintype V] in
theorem blockPermutation_apply (i : V ⊕ U) (j : U ⊕ V) :
    blockPermutation (K := K) (D := D) i j =
      if i = Equiv.sumComm U V j then 1 else 0 := by
  cases i <;> cases j <;> simp [blockPermutation, Matrix.one_apply]

omit [Fintype U] [Fintype V] in
theorem blockPermutation_reindex (e : (U ⊕ V) ≃ (V ⊕ U)) :
    (blockPermutation (K := K) (D := D)).submatrix id e.symm =
      permMatrix (e.symm.trans (Equiv.sumComm U V)) := by
  funext i j
  simp only [Matrix.submatrix_apply, id_eq, blockPermutation_apply,
    permMatrix_apply, Equiv.trans_apply]
  rfl

theorem theta_reindexed (f : Matrix V U (Laurent K D)) (g : Matrix U V (Laurent K D))
    (e : (U ⊕ V) ≃ (V ⊕ U)) :
    (Stabilization.theta f g).submatrix id e.symm =
      upper f * lower (-g) * permMatrix (e.symm.trans (Equiv.sumComm U V)) := by
  rw [Stabilization.theta_factorization]
  change ((upper f * lower (-g)) * blockPermutation).submatrix id e.symm = _
  rw [Matrix.submatrix_mul _ _ id id e.symm Function.bijective_id,
    Matrix.submatrix_id_id, blockPermutation_reindex]

/-- Every signed stabilization matrix is realized by a finite list of actual
SUM and SWAP layers. Each layer has disjoint site pairs, commutes with lattice
translations at the label level, and has the finite displacement bound below.
Both the source and target index types may be empty. -/
theorem theta_circuit (f : Matrix V U (Laurent K D)) (g : Matrix U V (Laurent K D))
    (e : (U ⊕ V) ≃ (V ⊕ U)) :
    ∃ c : List (Layer K D (V ⊕ U)),
      wordZ c = (Stabilization.theta f g).submatrix id e.symm ∧
      wordX c = dagger ((Stabilization.theta g f).submatrix e.symm id) ∧
      ∃ depth range : ℕ, depth = c.length ∧
        ∀ gate ∈ c, ∀ i : Fin D, (gate.displacement i).natAbs ≤ range := by
  obtain ⟨a, ha⟩ := two_shear_z_compilation (-g) f
  obtain ⟨b, hb⟩ := permutation_compilation (K := K) (D := D)
    (e.symm.trans (Equiv.sumComm U V))
  let c := a.map Layer.sum ++ b.map (Layer.swap (K := K) (D := D))
  have hc : wordZ c = (Stabilization.theta f g).submatrix id e.symm := by
    rw [theta_reindexed]
    change wordZ (a.map Layer.sum ++ b.map Layer.swap) = _
    rw [wordZ_append, wordZ_sum, wordZ_swap, ha, hb]
  have hinv : (Stabilization.theta f g).submatrix id e.symm *
      (Stabilization.theta g f).submatrix e.symm id = 1 := by
    rw [Matrix.submatrix_mul_equiv, Stabilization.theta_mul_reverse,
      Matrix.submatrix_id_id]
  exact ⟨c, hc, wordX_eq_dagger_inverse c _ _ hc hinv, word_finite_depth_range c⟩

end Decoupling.HighDim.Circuit
