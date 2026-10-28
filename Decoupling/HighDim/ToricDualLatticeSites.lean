import Decoupling.HighDim.ToricDualLatticeTransport

/-!
# The actual dual-cell sites and finite displacement

Complementation relabels cell species and the proved monomial factor
moves its lattice anchor by the sum of its coordinate directions.
Every displacement coordinate is 0 or 1. The resulting map of all
physical sites is a translation-covariant bijection.
-/

namespace Decoupling.HighDim.Toric

open Koszul Matrix

noncomputable section
attribute [local instance] Classical.propDecidable
variable {D k l : ℕ}

def cellTranslation (I : Cell D k) : Translation D := ∑ i : Fin k, translationBasis (I i)

theorem cellTranslation_apply (I : Cell D k) (x : Fin D) :
    cellTranslation I x = if x ∈ Hodge.directions I then 1 else 0 := by
  classical
  simp only [cellTranslation, Finset.sum_apply, translationBasis, Pi.single_apply]
  by_cases hx : x ∈ Hodge.directions I
  · obtain ⟨i, rfl⟩ := (Hodge.mem_directions I x).mp hx
    simp only [hx, ite_true]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j hj hji
      simp [Ne.symm hji]
    · simp
  · simp only [hx, ite_false]
    apply Finset.sum_eq_zero
    intro i hi
    have hix : I i ≠ x := by
      intro he
      exact hx ((Hodge.mem_directions I x).mpr ⟨i, he⟩)
    simp [Ne.symm hix]

theorem cellTranslation_range (I : Cell D k) (x : Fin D) :
    (cellTranslation I x).natAbs ≤ 1 := by
  rw [cellTranslation_apply]
  split <;> norm_num

def dualSiteEquiv (h : k + l = D) :
    (Cell D k × Translation D) ≃ (Cell D l × Translation D) where
  toFun x := (Hodge.complement h x.1, x.2 + cellTranslation x.1)
  invFun x := ((Hodge.complementEquiv h).symm x.1,
    x.2 - cellTranslation ((Hodge.complementEquiv h).symm x.1))
  left_inv x := by
    change ((Hodge.complementEquiv h).symm ((Hodge.complementEquiv h) x.1),
      x.2 + cellTranslation x.1 -
        cellTranslation ((Hodge.complementEquiv h).symm ((Hodge.complementEquiv h) x.1))) = x
    simp
  right_inv x := by
    change ((Hodge.complementEquiv h) ((Hodge.complementEquiv h).symm x.1),
      x.2 - cellTranslation ((Hodge.complementEquiv h).symm x.1) +
        cellTranslation ((Hodge.complementEquiv h).symm x.1)) = x
    simp

theorem dualSiteEquiv_translation (h : k + l = D) (I : Cell D k)
    (n a : Translation D) :
    dualSiteEquiv h (I, n + a) = ((dualSiteEquiv h (I, n)).1,
      (dualSiteEquiv h (I, n)).2 + a) := by
  simp [dualSiteEquiv, add_comm, add_left_comm]

theorem dualSiteEquiv_range (h : k + l = D) (I : Cell D k)
    (n : Translation D) (x : Fin D) :
    (((dualSiteEquiv h (I, n)).2 - n) x).natAbs ≤ 1 := by
  simpa [dualSiteEquiv] using cellTranslation_range I x

variable (K : Type) [CommRing K]

private theorem prod_monomial {ι : Type*} (s : Finset ι) (a : ι → Translation D) :
    (∏ i ∈ s, monomial K (a i)) = monomial K (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

theorem cellUnit_monomial (I : Cell D k) :
    (Hodge.cellUnit (Laurent K D) (Hodge.directionUnit K) I : Laurent K D) =
      (-1 : Laurent K D) ^ k * monomial K (cellTranslation I) := by
  simp only [Hodge.cellUnit, Units.coe_prod]
  change (∏ i : Fin k, -monomial K (translationBasis (I i))) = _
  rw [Finset.prod_neg]
  simp only [Finset.card_univ, Fintype.card_fin]
  rw [prod_monomial]
  rfl

/-- Every actual qudit coefficient is the signed monomial of its proved
physical displacement; no unexplained Laurent unit is assumed. -/
theorem dualCellUnit_monomial (I : Cell D k) :
    (dualCellUnit K I : Laurent K D) =
      (-1 : Laurent K D) ^ ((∑ x ∈ Hodge.directions I, x.val) + k) *
        monomial K (cellTranslation I) := by
  change Hodge.orientation (Laurent K D) I *
    (Hodge.cellUnit (Laurent K D) (Hodge.directionUnit K) I : Laurent K D) = _
  rw [cellUnit_monomial, pow_add]
  exact (mul_assoc _ _ _).symm

/-- The Laurent matrix sends a single physical site to exactly its dual
site, with the explicit orientation sign. -/
theorem dualLatticeMatrix_site (h : k + l = D) (I : Cell D k) (n : Translation D) :
    dualLatticeMatrix K h *ᵥ Pi.single ((Fintype.equivFin (Cell D k)) I) (monomial K n) =
      Pi.single ((Fintype.equivFin (Cell D l)) (dualSiteEquiv h (I, n)).1)
        ((-1 : Laurent K D) ^ ((∑ x ∈ Hodge.directions I, x.val) + k) *
          monomial K (dualSiteEquiv h (I, n)).2) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, dualLatticeMatrix_entry,
    Equiv.symm_apply_apply, dualCellUnit_monomial]
  have he : complementaryIndex h ((Fintype.equivFin (Cell D k)) I) =
      (Fintype.equivFin (Cell D l)) (Hodge.complement h I) := by
    simp [complementaryIndex, Hodge.complementEquiv]
  rw [he]
  change (if (Fintype.equivFin (Cell D l)) (Hodge.complement h I) = i then
    (-1 : Laurent K D) ^ ((∑ x ∈ Hodge.directions I, x.val) + k) *
      monomial K (cellTranslation I) else 0) * monomial K n =
      if i = (Fintype.equivFin (Cell D l)) (Hodge.complement h I) then _ else 0
  by_cases hi : (Fintype.equivFin (Cell D l)) (Hodge.complement h I) = i
  · simp only [hi, ite_true]
    rw [mul_assoc, monomial_mul]
    simp [dualSiteEquiv, add_comm]
  · simp [hi, Ne.symm hi]

end
end Decoupling.HighDim.Toric
