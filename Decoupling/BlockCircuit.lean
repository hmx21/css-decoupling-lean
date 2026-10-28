import Decoupling.Onsite

/-!
# Circuit realization of the stable block matrix

The source and target of 𝒮(f,g) have opposite direct-sum orders. An explicit
equivalence `e` identifies source species with target species for circuit
execution. The theorem holds for every such identification; the resulting
onsite permutation is compiled by the previously proved SWAP implementation.
-/

namespace Decoupling.Circuit

open Matrix

noncomputable section

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

def blockPermutation : Matrix (V ⊕ U) (U ⊕ V) R :=
  fromBlocks 0 1 1 0

omit [Fintype U] [Fintype V] in
theorem blockPermutation_apply (i : V ⊕ U) (j : U ⊕ V) :
    blockPermutation i j = if i = Equiv.sumComm U V j then 1 else 0 := by
  cases i <;> cases j <;> simp [blockPermutation, Matrix.one_apply]

omit [Fintype U] [Fintype V] in
theorem blockPermutation_reindex (e : (U ⊕ V) ≃ (V ⊕ U)) :
    blockPermutation.submatrix id e.symm =
      permMatrix (e.symm.trans (Equiv.sumComm U V)) := by
  funext i j
  simp only [Matrix.submatrix_apply, id_eq, blockPermutation_apply,
    permMatrix_apply, Equiv.trans_apply]
  rfl

theorem block_reindexed (f : Matrix U V R) (g : Matrix V U R)
    (e : (U ⊕ V) ≃ (V ⊕ U)) :
    (Stabilization.block f g).submatrix id e.symm =
      upper g * lower f * permMatrix (e.symm.trans (Equiv.sumComm U V)) := by
  rw [Stabilization.block_factorization]
  change ((upper g * lower f) * blockPermutation).submatrix id e.symm = _
  rw [Matrix.submatrix_mul _ _ id id e.symm Function.bijective_id,
    Matrix.submatrix_id_id, blockPermutation_reindex]

/-- Proposition IV.3 for the actual block matrix: a finite CNOT/SWAP circuit,
with the manuscript's Z action and an explicit common species coordinate order.
Each listed family is depth one by `CNOT.disjoint_gates`; `depth` and `range`
are finite input-dependent bounds, with no system-size parameter. -/
theorem block_circuit (f : Matrix U V R) (g : Matrix V U R)
    (e : (U ⊕ V) ≃ (V ⊕ U)) :
    ∃ c : List (CNOT (V ⊕ U)),
      zAction c = (Stabilization.block f g).submatrix id e.symm ∧
      xAction c = dagger ((Stabilization.block g f).submatrix e.symm id) ∧
      ∃ depth range : ℕ, depth = c.length ∧
        ∀ gate ∈ c, ∀ i : Fin 3, (gate.displacement i).natAbs ≤ range := by
  obtain ⟨a, ha⟩ := two_shear_compilation f g
  obtain ⟨b, hb, _⟩ := permutation_compilation (e.symm.trans (Equiv.sumComm U V))
  let c := (a ++ b).map CNOT.dual
  have hc : zAction c = (Stabilization.block f g).submatrix id e.symm := by
    rw [block_reindexed]
    change zAction ((a ++ b).map CNOT.dual) = _
    rw [zAction_dual, xAction_append, ha, hb]
  have hinv : (Stabilization.block f g).submatrix id e.symm *
      (Stabilization.block g f).submatrix e.symm id = 1 := by
    rw [Matrix.submatrix_mul_equiv, Stabilization.block_mul_reverse,
      Matrix.submatrix_id_id]
  exact ⟨c, hc, xAction_eq_dagger_inverse c _ _ hc hinv, finite_depth_range c⟩

end
end Decoupling.Circuit
