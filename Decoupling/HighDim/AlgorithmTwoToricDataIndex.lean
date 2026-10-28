import Decoupling.HighDim.AlgorithmTwoToricDataCells
import Mathlib.Algebra.BigOperators.Fin

/-!
# Executable total index for the computed toric stack

Copies use the explicit finite sigma enumeration. Each copy has all
`2^D` subset cells, and the stored integer degree is `j+1-|I|`.
All constructions here read natural-number dimensions only.
-/
namespace Decoupling.HighDim.AlgorithmTwoToricData
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def multiplicities (D : ℕ) (t : Vector ℕ (D - 1)) (j : Fin (D - 1)) : ℕ := t[j]

abbrev Copy (D : ℕ) (t : Vector ℕ (D - 1)) := Σ j : Fin (D - 1), Fin (multiplicities D t j)

def copyCount (D : ℕ) (t : Vector ℕ (D - 1)) : ℕ := ∑ j, multiplicities D t j

def totalRank (D : ℕ) (t : Vector ℕ (D - 1)) : ℕ := copyCount D t * 2 ^ D

def copyEquiv (D : ℕ) (t : Vector ℕ (D - 1)) : Fin (copyCount D t) ≃ Copy D t :=
  finSigmaFinEquiv.symm

def labelEquiv (D : ℕ) (t : Vector ℕ (D - 1)) :
    Fin (totalRank D t) ≃ Copy D t × Fin (2 ^ D) :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (copyEquiv D t) (Equiv.refl _))

def labelDegree (D : ℕ) (t : Vector ℕ (D - 1)) (i : Fin (totalRank D t)) : ℤ :=
  let a := labelEquiv D t i
  (a.1.1.val : ℤ) + 1 - (subsetAt D a.2).card

def degrees (D : ℕ) (t : Vector ℕ (D - 1)) : Vector ℤ (totalRank D t) :=
  Vector.ofFn (labelDegree D t)

@[simp] theorem degrees_get (D : ℕ) (t : Vector ℕ (D - 1)) (i : Fin (totalRank D t)) :
    (degrees D t).get i = labelDegree D t i := by
  change (Vector.ofFn (labelDegree D t))[i.val] = _
  simp

def topLabel (D : ℕ) (t : Vector ℕ (D - 1)) (i : Copy D t) : Fin (totalRank D t) :=
  (labelEquiv D t).symm (i, subsetIndex D ∅)

theorem topLabel_degree (D : ℕ) (t : Vector ℕ (D - 1)) (i : Copy D t) :
    (degrees D t).get (topLabel D t i) = (i.1.val : ℤ) + 1 := by
  simp [labelDegree, topLabel, subsetAt_index]

theorem degree_bounds (D : ℕ) (t : Vector ℕ (D - 1)) (i : Fin (totalRank D t)) :
    -(D : ℤ) ≤ (degrees D t).get i ∧ (degrees D t).get i ≤ D := by
  rw [degrees_get]
  have hj := (labelEquiv D t i).1.1.isLt
  have hc := cell_card_le D (labelEquiv D t i).2
  dsimp [labelDegree]
  omega

theorem totalRank_eq (D : ℕ) (t : Vector ℕ (D - 1)) :
    totalRank D t = 2 ^ D * ∑ j : Fin (D - 1), t[j] := by
  simp only [totalRank, copyCount, multiplicities, Nat.mul_comm]

end Decoupling.HighDim.AlgorithmTwoToricData
