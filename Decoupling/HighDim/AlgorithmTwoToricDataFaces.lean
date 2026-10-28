import Decoupling.HighDim.AlgorithmTwoToricDataCells
import Mathlib.Algebra.Ring.Parity

/-!
# Executable oriented face selection

The direction is found by a finite scan of integer labels. A cache
containing minus one supplies all alternating signs by a parity
test; no field exponentiation is executed.
-/
namespace Decoupling.HighDim.AlgorithmTwoToricData
open Koszul
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def removedDirection {D : ℕ} (row col : Finset (Fin D)) : Option (Fin D) :=
  (List.finRange D).find? (fun i => decide (i ∈ col ∧ col.erase i = row))

theorem removedDirection_none_iff {D : ℕ} (row col : Finset (Fin D)) :
    removedDirection row col = none ↔ ¬ ∃ i ∈ col, col.erase i = row := by
  simp [removedDirection, List.find?_eq_none]

theorem removedDirection_some_imp {D : ℕ} (row col : Finset (Fin D)) (i : Fin D)
    (he : removedDirection row col = some i) : i ∈ col ∧ col.erase i = row := by
  exact of_decide_eq_true (List.find?_some
    (p := fun a : Fin D => decide (a ∈ col ∧ col.erase a = row)) he)

theorem removedDirection_some_iff {D : ℕ} (row col : Finset (Fin D)) (i : Fin D) :
    removedDirection row col = some i ↔ i ∈ col ∧ col.erase i = row := by
  constructor
  · exact removedDirection_some_imp row col i
  · intro hi
    have hn : removedDirection row col ≠ none :=
      fun he => (removedDirection_none_iff row col).mp he ⟨i, hi⟩
    cases he : removedDirection row col with
    | none => exact False.elim (hn he)
    | some j =>
      have hj := removedDirection_some_imp row col j he
      have hji : j = i := (Finset.erase_inj col hj.1).mp (hj.2.trans hi.2.symm)
      subst j
      rfl

def cachedSign {K : Type*} [One K] (minusOne : K) (n : ℕ) : K :=
  if n % 2 = 0 then 1 else minusOne

theorem cachedSign_eq {K : Type*} [Ring K] (n : ℕ) :
    cachedSign (-1 : K) n = (-1 : K) ^ n := by
  rw [neg_one_pow_eq_ite]
  simp [cachedSign, Nat.even_iff]

theorem cachedSign_succ {K : Type*} [Ring K] (n : ℕ) :
    cachedSign (-1 : K) (n + 1) = -cachedSign (-1 : K) n := by
  rw [cachedSign_eq, cachedSign_eq, pow_succ, mul_neg_one]

theorem removedDirection_native_face {D k : ℕ} (I : Cell D (k + 1)) (i : Fin (k + 1)) :
    removedDirection (cellSet (face I i)) (cellSet I) = some (I i) := by
  apply (removedDirection_some_iff _ _ _).mpr
  exact ⟨Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩, (cellSet_face I i).symm⟩

theorem removedDirection_card {D : ℕ} {row col : Finset (Fin D)} {i : Fin D}
    (h : removedDirection row col = some i) : row.card + 1 = col.card := by
  obtain ⟨hi, he⟩ := removedDirection_some_imp row col i h
  rw [← he, Finset.card_erase_of_mem hi]
  have : 0 < col.card := Finset.card_pos.mpr ⟨i, hi⟩
  omega

end Decoupling.HighDim.AlgorithmTwoToricData
