import Decoupling.HighDim.ToricHodgeCells
import Mathlib.Data.Finset.Powerset

/-!
# Counting cells and isolating a single Koszul face

Source: Appendix B.3. These finite combinatorial facts hold in every
ambient dimension. In particular, distinct deletions of an ordered cell
cannot cancel one another in a Koszul differential.
-/

namespace Decoupling.HighDim.Torus

open Koszul Toric.Hodge
noncomputable section

/-- Ordered cells are exactly cardinality-`k` subsets of the directions. -/
def cellSubsetEquiv (D k : ℕ) : Cell D k ≃ {s : Finset (Fin D) // s.card = k} where
  toFun I := ⟨directions I, directions_card I⟩
  invFun s := s.val.orderEmbOfFin s.property
  left_inv I := by
    apply directions_injective
    exact Finset.map_orderEmbOfFin_univ _ _
  right_inv s := by
    apply Subtype.ext
    exact Finset.map_orderEmbOfFin_univ _ _

@[simp] theorem card_cell (D k : ℕ) : Fintype.card (Cell D k) = D.choose k := by
  rw [Fintype.card_congr (cellSubsetEquiv D k), Fintype.card_finset_len, Fintype.card_fin]

/-- Any direction lies in some cell of every positive admissible degree. -/
theorem exists_cell_containing {D k : ℕ} (hk : 1 ≤ k) (hkD : k ≤ D) (a : Fin D) :
    ∃ (I : Cell D k) (i : Fin k), I i = a := by
  classical
  obtain ⟨s, hs, hcard⟩ := Finset.exists_superset_card_eq
    (s := {a}) (n := k) (by simpa using hk) (by simpa using hkD)
  let I : Cell D k := s.orderEmbOfFin hcard
  have ha : a ∈ directions I := by
    have hd : directions I = s := Finset.map_orderEmbOfFin_univ _ _
    rw [hd]
    exact hs (by simp)
  obtain ⟨i, hi⟩ := (mem_directions I a).mp ha
  exact ⟨I, i, hi⟩

/-- Distinct deleted positions give distinct output cells. -/
theorem face_injective {D k : ℕ} (I : Cell D (k + 1)) :
    Function.Injective (face I) := by
  classical
  intro i j h
  by_contra hij
  have hi : I i ∈ directions (face I j) := by
    rw [directions_face, Finset.mem_erase]
    exact ⟨I.injective.ne hij, (mem_directions I _).mpr ⟨i, rfl⟩⟩
  rw [← h, directions_face] at hi
  exact (Finset.mem_erase.mp hi).1 rfl

/-- Coordinate extraction from the signed boundary has a single term. -/
theorem boundary_coefficient {A : Type*} [CommRing A] {D k : ℕ}
    (w : Fin D → A) (I : Cell D (k + 1)) (i : Fin (k + 1)) :
    boundary A w k (Finsupp.single I 1) (face I i) = (-1 : A) ^ i.val * w (I i) := by
  classical
  rw [boundary_basis]
  simp only [Finsupp.finsetSum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    simp [(face_injective I).ne hji]
  · simp

end
end Decoupling.HighDim.Torus
