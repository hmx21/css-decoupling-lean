import Decoupling.HighDim.AlgorithmTwoToricDataCoefficients

/-! # The lookup face array is the actual signed Koszul boundary -/
namespace Decoupling.HighDim.AlgorithmTwoToricData
open CategoryTheory Koszul
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
noncomputable section
variable {K : Type} [Field K] {D k : ℕ}

theorem cellSet_injective : Function.Injective (cellSet (D := D) (k := k)) :=
  Toric.Hodge.directions_injective

theorem face_injective (I : Cell D (k + 1)) : Function.Injective (face I) := by
  intro i j he
  apply I.injective
  apply (Finset.erase_inj (cellSet I) (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)).mp
  change (cellSet I).erase (I i) = (cellSet I).erase (I j)
  rw [← cellSet_face, ← cellSet_face, he]

/-- Full coefficient equality, not merely equality of zero loci.
The row and column are genuine ordered native Koszul cells. -/
theorem faceDense_boundary (J : Cell D k) (I : Cell D (k + 1)) :
    LaurentArithmetic.denote (faceDense (-1 : K) (cellSet J) (cellSet I)) =
      (show Term (Laurent K D) D k from
        boundary (Laurent K D) (difference K) k (Finsupp.single I 1)) J := by
  classical
  rw [boundary_basis]
  simp only [Finsupp.finsetSum_apply, Finsupp.single_apply]
  cases he : removedDirection (cellSet J) (cellSet I) with
  | none =>
    rw [faceDense_none he]
    symm
    apply Finset.sum_eq_zero
    intro i _
    have hne : face I i ≠ J := by
      intro hi
      have hh := removedDirection_native_face I i
      rw [hi, he] at hh
      cases hh
    simp [hne]
  | some a =>
    obtain ⟨ha, herase⟩ := removedDirection_some_imp (cellSet J) (cellSet I) a he
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp ha
    change I i = a at hi
    subst a
    have hface : face I i = J := by
      apply cellSet_injective
      rw [cellSet_face, herase]
    rw [faceDense_some he, cellPosition_ordered, cachedSign_eq]
    rw [Finset.sum_eq_single i]
    · rw [hface]
      have hconst : constant ((-1 : K) ^ i.val) = (-1 : Laurent K D) ^ i.val := by
        rw [map_pow, map_neg, map_one]
      rw [hconst]
      simp
    · intro l _ hli
      have hne : face I l ≠ J := by
        intro h
        exact hli (face_injective I (h.trans hface.symm))
      simp [hne]
    · simp

end
end Decoupling.HighDim.AlgorithmTwoToricData
