import Decoupling.HighDim.AlgorithmTwoFiniteComplexBounded
import Decoupling.HighDim.AlgorithmTwoLinearComparisonCompile

/-!
# Pure placement of original degree-slot columns into total coordinates

Each input is a materialized dependent column: an integer degree slot
and a dense array in that original term basis. Placement only copies
coefficients or inserts zero, so it performs zero field operations.
-/
namespace Decoupling.HighDim.AlgorithmTwoFiniteComplex
open CategoryTheory ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D h length count : ℕ}

structure SlotColumn (K : Type*) (D h : ℕ) {length : ℕ} (rank : Fin length → ℕ) where
  slot : Fin length
  entries : Vector (LaurentArithmetic.Dense K D h) (rank slot)

def placeColumn {rank : Fin length → ℕ} (c : SlotColumn K D h rank) :
    Vector (LaurentArithmetic.Dense K D h) (∑ i, rank i) :=
  Vector.ofFn fun i =>
    let row := (finSigmaFinEquiv (n := rank)).symm i
    if hr : row.1 = c.slot then c.entries[Fin.cast (congrArg rank hr) row.2]
    else AlgorithmTwoLinearComparison.zeroDense

def placeColumns {rank : Fin length → ℕ} (columns : Vector (SlotColumn K D h rank) count) :
    LaurentArithmetic.DenseMatrix K D (∑ i, rank i) count h :=
  Vector.ofFn fun i => Vector.ofFn fun j => (placeColumn columns[j])[i]

def placementProgram {rank : Fin length → ℕ} (columns : Vector (SlotColumn K D h rank) count) :
    Work K (LaurentArithmetic.DenseMatrix K D (∑ i, rank i) count h) :=
  Work.pure (placeColumns columns)

@[simp] theorem placementProgram_cost {rank : Fin length → ℕ}
    (columns : Vector (SlotColumn K D h rank) count) : (placementProgram columns).cost = 0 := rfl

theorem placeColumn_at {rank : Fin length → ℕ} (c : SlotColumn K D h rank)
    (i : Fin length) (a : Fin (rank i)) :
    (placeColumn c)[finSigmaFinEquiv ⟨i,a⟩] =
      if hi : i = c.slot then c.entries[Fin.cast (congrArg rank hi) a]
        else AlgorithmTwoLinearComparison.zeroDense := by
  simp only [placeColumn, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Equiv.symm_apply_apply]
  split_ifs with hi
  · apply congrArg (fun b : Fin (rank c.slot) => c.entries[b])
    apply Fin.ext
    change (((finSigmaFinEquiv (n := rank)).symm ((finSigmaFinEquiv (n := rank)) ⟨i,a⟩)).2).val = a.val
    rw [Equiv.symm_apply_apply]
  · rfl

noncomputable section
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}

theorem bounded_embed_at (c : StableFree.Coordinates C) (lo : ℤ) (length : ℕ)
    (outside : ∀ j, j < lo ∨ lo+length ≤ j → c.rank j = 0)
    (j : ℤ) (x : C.X j) (i : Fin length) (a : Fin (c.rank (lo+i))) :
    (Coordinates.ofBounded c lo length outside).embed j x (finSigmaFinEquiv ⟨i,a⟩) =
      if hi : lo+(i:ℤ) = j then (c.equiv j x) (Fin.cast (congrArg c.rank hi) a) else 0 := by
  simp only [Coordinates.ofBounded, Coordinates.ofDegreewise, LinearMap.comp_apply,
    LinearEquiv.coe_coe, fiberEmbed, LinearMap.coe_mk, AddHom.coe_mk]
  by_cases hi : lo+(i:ℤ) = j
  · rw [dite_eq_left ((totalDegree_at c.rank lo length ⟨i,a⟩).trans hi), dite_eq_left hi]
    change (c.equiv j x) (fiberIndexEquiv c.rank lo length outside j ⟨finSigmaFinEquiv ⟨i,a⟩, _⟩) = _
    apply congrArg (c.equiv j x)
    apply Fin.ext
    change (((finSigmaFinEquiv (n := fun s : Fin length => c.rank (lo+s))).symm
      ((finSigmaFinEquiv (n := fun s : Fin length => c.rank (lo+s))) ⟨i,a⟩)).2).val = a.val
    rw [Equiv.symm_apply_apply]
  · rw [dite_eq_right (by simpa only [totalDegree_at] using hi), dite_eq_right hi]

theorem placeColumn_native (c : StableFree.Coordinates C) (lo : ℤ) (length : ℕ)
    (outside : ∀ j, j < lo ∨ lo+length ≤ j → c.rank j = 0)
    (column : SlotColumn K D h (fun i : Fin length => c.rank (lo+i))) :
    (fun a => LaurentArithmetic.denote (placeColumn column)[a]) =
      (Coordinates.ofBounded c lo length outside).embed (lo+column.slot)
        ((c.equiv (lo+column.slot)).symm (fun i => LaurentArithmetic.denote column.entries[i])) := by
  funext a
  obtain ⟨⟨i,r⟩,rfl⟩ := (finSigmaFinEquiv (n := fun i : Fin length => c.rank (lo+i))).surjective a
  rw [placeColumn_at, bounded_embed_at]
  by_cases hi : i = column.slot
  · subst i
    simp
  · have hd : lo+(i:ℤ) ≠ lo+column.slot := by intro hd; apply hi; apply Fin.ext; omega
    rw [dite_eq_right hi, dite_eq_right hd, AlgorithmTwoLinearComparison.zeroDense_correct]

theorem placeColumns_native (c : StableFree.Coordinates C) (lo : ℤ) (length : ℕ)
    (outside : ∀ j, j < lo ∨ lo+length ≤ j → c.rank j = 0)
    (columns : Vector (SlotColumn K D h (fun i : Fin length => c.rank (lo+i))) count)
    (j : Fin count) :
    (fun a => LaurentArithmetic.matrixDenote (placeColumns columns) a j) =
      (Coordinates.ofBounded c lo length outside).embed (lo+columns[j].slot)
        ((c.equiv (lo+columns[j].slot)).symm (fun i => LaurentArithmetic.denote columns[j].entries[i])) := by
  funext a
  simp only [LaurentArithmetic.matrixDenote, placeColumns, Fin.getElem_fin, Vector.getElem_ofFn]
  exact congrFun (placeColumn_native c lo length outside columns[j]) a

end
end Decoupling.HighDim.AlgorithmTwoFiniteComplex
