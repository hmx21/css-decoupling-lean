import Decoupling.HighDim.ToricDualLatticeMatrix

/-!
# The dual-cell matrix preserves the Laurent Hermitian pairing

Every nonzero entry is a proved signed unit monomial and every row and
column contains exactly one such entry. Both dagger inverse identities
are proved, including the empty-cell case.
-/

namespace Decoupling.HighDim.Toric

open Matrix Koszul

noncomputable section
attribute [local instance] Classical.propDecidable
variable (K : Type) [CommRing K] {D k l : ℕ}

theorem directionUnit_bar_mul (i : Fin D) :
    bar (Hodge.directionUnit K i : Laurent K D) * (Hodge.directionUnit K i : Laurent K D) = 1 := by
  change bar (-coordinate K i) * (-coordinate K i) = 1
  simp [coordinate]

theorem cellUnit_bar_mul (I : Cell D k) :
    bar (Hodge.cellUnit (Laurent K D) (Hodge.directionUnit K) I : Laurent K D) *
      (Hodge.cellUnit (Laurent K D) (Hodge.directionUnit K) I : Laurent K D) = 1 := by
  have hp : (Hodge.cellUnit (Laurent K D) (Hodge.directionUnit K) I : Laurent K D) =
      ∏ i : Fin k, (Hodge.directionUnit K (I i) : Laurent K D) :=
    map_prod (Units.coeHom (Laurent K D)) _ _
  rw [hp, map_prod, ← Finset.prod_mul_distrib]
  simp [directionUnit_bar_mul]

theorem dualCellUnit_bar_mul (I : Cell D k) :
    bar (dualCellUnit K I : Laurent K D) * (dualCellUnit K I : Laurent K D) = 1 := by
  have ho : bar (Hodge.orientation (Laurent K D) I) = Hodge.orientation (Laurent K D) I := by
    simp [Hodge.orientation]
  change bar (Hodge.orientation (Laurent K D) I *
      (Hodge.cellUnit (Laurent K D) (Hodge.directionUnit K) I : Laurent K D)) *
    (Hodge.orientation (Laurent K D) I *
      (Hodge.cellUnit (Laurent K D) (Hodge.directionUnit K) I : Laurent K D)) = 1
  rw [bar_mul, ho]
  calc
    _ = (Hodge.orientation (Laurent K D) I * Hodge.orientation (Laurent K D) I) *
        (bar (Hodge.cellUnit (Laurent K D) (Hodge.directionUnit K) I : Laurent K D) *
          (Hodge.cellUnit (Laurent K D) (Hodge.directionUnit K) I : Laurent K D)) := by ring
    _ = 1 := by rw [Hodge.orientation_sq, cellUnit_bar_mul, one_mul]

theorem dualLatticeMatrix_dagger_mul (h : k + l = D) :
    dagger (dualLatticeMatrix K h) * dualLatticeMatrix K h = 1 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  simp only [dagger_apply, dualLatticeMatrix_entry, apply_ite bar, bar_zero]
  rw [Finset.sum_eq_single (complementaryIndex h i)]
  · by_cases hij : i = j
    · subst j
      simp [dualCellUnit_bar_mul]
    · have hij' : complementaryIndex h j ≠ complementaryIndex h i :=
        (complementaryIndex h).injective.ne (Ne.symm hij)
      simp [hij, hij']
  · intro b hb hbne
    simp [Ne.symm hbne]
  · simp

theorem dualLatticeMatrix_mul_dagger (h : k + l = D) :
    dualLatticeMatrix K h * dagger (dualLatticeMatrix K h) = 1 := by
  apply Matrix.ext
  intro i j
  rw [Matrix.mul_apply]
  simp only [dagger_apply, dualLatticeMatrix_entry, apply_ite bar, bar_zero]
  rw [Finset.sum_eq_single ((complementaryIndex h).symm i)]
  · by_cases hij : i = j
    · subst j
      simp only [Equiv.apply_symm_apply, ite_true, Matrix.one_apply_eq]
      rw [mul_comm, dualCellUnit_bar_mul]
    · simp [hij]
  · intro b hb hbne
    have hb' : complementaryIndex h b ≠ i := by
      intro he
      exact hbne ((complementaryIndex h).injective (he.trans ((complementaryIndex h).apply_symm_apply i).symm))
    simp [hb']
  · simp

end
end Decoupling.HighDim.Toric
