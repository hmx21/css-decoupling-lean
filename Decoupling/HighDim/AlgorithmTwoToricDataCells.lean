import Decoupling.HighDim.ToricHodgeCells
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

/-!
# Executable bit-mask enumeration of all ordered toric cells

The enumeration depends only on the spatial dimension. It uses no
field value, basis choice, or `Fintype.equivFin` selection. The native
Koszul cell is the increasing enumeration of the computed subset.
-/
namespace Decoupling.HighDim.AlgorithmTwoToricData
open Koszul
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def subsetAt (D : ℕ) (a : Fin (2 ^ D)) : Finset (Fin D) :=
  Finset.univ.filter (fun i => (finFunctionFinEquiv.symm a : Fin D → Fin 2) i = 1)

def subsetIndex (D : ℕ) (s : Finset (Fin D)) : Fin (2 ^ D) :=
  finFunctionFinEquiv (fun i => if i ∈ s then (1 : Fin 2) else 0)

theorem subsetAt_index (D : ℕ) (s : Finset (Fin D)) : subsetAt D (subsetIndex D s) = s := by
  ext i
  by_cases hi : i ∈ s <;> simp [subsetAt, subsetIndex, hi]

theorem subsetIndex_at (D : ℕ) (a : Fin (2 ^ D)) : subsetIndex D (subsetAt D a) = a := by
  apply finFunctionFinEquiv.symm.injective
  simp only [subsetIndex, Equiv.symm_apply_apply]
  funext i
  generalize hx : (finFunctionFinEquiv.symm a : Fin D → Fin 2) i = x
  have hh : x = 0 ∨ x = 1 := by
    have := x.isLt
    rcases x with ⟨x, hx⟩
    rcases (show x = 0 ∨ x = 1 by omega) with h | h <;> simp [h]
  rcases hh with rfl | rfl <;> simp [subsetAt, hx]

def subsetEquiv (D : ℕ) : Fin (2 ^ D) ≃ Finset (Fin D) where
  toFun := subsetAt D
  invFun := subsetIndex D
  left_inv := subsetIndex_at D
  right_inv := subsetAt_index D

def cellSet {D k : ℕ} (I : Cell D k) : Finset (Fin D) := Finset.univ.map I.toEmbedding

@[simp] theorem cellSet_card {D k : ℕ} (I : Cell D k) : (cellSet I).card = k := by
  simp [cellSet]

def cellOfSet {D k : ℕ} (s : Finset (Fin D)) (h : s.card = k) : Cell D k :=
  s.orderEmbOfFin h

theorem cellSet_cellOfSet {D k : ℕ} (s : Finset (Fin D)) (h : s.card = k) :
    cellSet (cellOfSet s h) = s := Finset.map_orderEmbOfFin_univ s h

theorem cellOfSet_cellSet {D k : ℕ} (I : Cell D k) :
    cellOfSet (cellSet I) (cellSet_card I) = I := by
  symm
  exact Finset.orderEmbOfFin_unique' _ (fun i => Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)

def orderedCell (D : ℕ) (a : Fin (2 ^ D)) : Cell D (subsetAt D a).card :=
  cellOfSet (subsetAt D a) rfl

def orderedCellIndex {D k : ℕ} (I : Cell D k) : Fin (2 ^ D) := subsetIndex D (cellSet I)

theorem subsetAt_orderedCellIndex {D k : ℕ} (I : Cell D k) :
    subsetAt D (orderedCellIndex I) = cellSet I := subsetAt_index D _

/-- Zero-based position of a direction in the increasing cell. -/
def cellPosition {D : ℕ} (s : Finset (Fin D)) (i : Fin D) : ℕ :=
  (s.filter (fun j => j < i)).card

theorem cellPosition_ordered {D k : ℕ} (I : Cell D k) (i : Fin k) :
    cellPosition (cellSet I) (I i) = i.val := by
  rw [cellPosition, cellSet, Finset.filter_map]
  simp only [RelEmbedding.coe_toEmbedding, Function.comp_apply, I.lt_iff_lt, Finset.card_map]
  change (Finset.univ.filter (fun j : Fin k => j < i)).card = i.val
  rw [Finset.filter_gt_eq_Iio]
  simp

theorem cellSet_face {D k : ℕ} (I : Cell D (k + 1)) (i : Fin (k + 1)) :
    cellSet (face I i) = (cellSet I).erase (I i) :=
  Toric.Hodge.directions_face I i

theorem cell_card_le (D : ℕ) (a : Fin (2 ^ D)) : (subsetAt D a).card ≤ D := by
  simpa using Finset.card_le_univ (subsetAt D a)

/-- Computable native ordered-cell coordinates within one degree.
The subtype is determined solely by the popcount of an integer mask. -/
def cellMaskEquiv (D k : ℕ) :
    Cell D k ≃ {a : Fin (2 ^ D) // (subsetAt D a).card = k} where
  toFun I := ⟨orderedCellIndex I, by rw [subsetAt_orderedCellIndex, cellSet_card]⟩
  invFun a := cellOfSet (subsetAt D a.val) a.property
  left_inv I := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro i
    rw [subsetAt_orderedCellIndex]
    exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩
  right_inv a := by
    apply Subtype.ext
    apply (subsetEquiv D).injective
    change subsetAt D (orderedCellIndex (cellOfSet (subsetAt D a.val) a.property)) = subsetAt D a.val
    rw [subsetAt_orderedCellIndex, cellSet_cellOfSet]

@[simp] theorem cellMaskEquiv_value {D k : ℕ} (I : Cell D k) :
    (cellMaskEquiv D k I).val = orderedCellIndex I := rfl

end Decoupling.HighDim.AlgorithmTwoToricData
