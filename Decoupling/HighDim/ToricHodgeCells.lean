import Decoupling.HighDim.ToricWindow
import Mathlib.Data.Finset.Sort
import Mathlib.Order.Interval.Finset.Fin

/-!
# Complementary ordered cells for the toric Hodge correspondence

These are actual complements inside the finite coordinate-direction set.
The order and the deletion relation are proved before introducing any
duality map or differential identity.
-/

namespace Decoupling.HighDim.Toric.Hodge

open Koszul

noncomputable section
variable {D k l : ℕ}

def directions (I : Cell D k) : Finset (Fin D) := Finset.univ.map I.toEmbedding

@[simp] theorem directions_card (I : Cell D k) : (directions I).card = k := by
  simp [directions]

@[simp] theorem mem_directions (I : Cell D k) (x : Fin D) :
    x ∈ directions I ↔ ∃ i, I i = x := by simp [directions]

theorem directions_injective : Function.Injective (directions (D := D) (k := k)) := by
  intro I J h
  have hi : I = (directions J).orderEmbOfFin (directions_card J) := by
    apply Finset.orderEmbOfFin_unique'
    intro i
    rw [← h]
    exact (mem_directions I _).mpr ⟨i, rfl⟩
  have hj : J = (directions J).orderEmbOfFin (directions_card J) := by
    apply Finset.orderEmbOfFin_unique'
    intro i
    exact (mem_directions J _).mpr ⟨i, rfl⟩
  exact hi.trans hj.symm

/-- Complement a cell with the prescribed complementary cardinality. -/
def complement (h : k + l = D) (I : Cell D k) : Cell D l :=
  (directions I)ᶜ.orderEmbOfFin (by simp [Finset.card_compl]; omega)

@[simp] theorem directions_complement (h : k + l = D) (I : Cell D k) :
    directions (complement h I) = (directions I)ᶜ := by
  exact Finset.map_orderEmbOfFin_univ _ _

theorem complement_involutive (h : k + l = D) (I : Cell D k) :
    complement (by omega : l + k = D) (complement h I) = I := by
  apply directions_injective
  simp

def complementEquiv (h : k + l = D) : Cell D k ≃ Cell D l where
  toFun := complement h
  invFun := complement (by omega)
  left_inv := complement_involutive h
  right_inv := complement_involutive (by omega)

theorem directions_face (I : Cell D (k + 1)) (i : Fin (k + 1)) :
    directions (face I i) = (directions I).erase (I i) := by
  ext x
  simp only [mem_directions, Finset.mem_erase]
  constructor
  · rintro ⟨j, rfl⟩
    refine ⟨?_, ⟨i.succAbove j, rfl⟩⟩
    exact fun h => Fin.succAbove_ne i j (I.injective h)
  · rintro ⟨hne, ⟨j, rfl⟩⟩
    obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq (fun h => hne (congrArg I h))
    exact ⟨a, congrArg I ha⟩

theorem directions_complement_face (h : k + 1 + l = D)
    (I : Cell D (k + 1)) (i : Fin (k + 1)) :
    directions (complement (by omega : k + (l + 1) = D) (face I i)) =
      insert (I i) (directions (complement h I)) := by
  simp [directions_face, Finset.compl_erase]

/-- The increasing-coordinate rank equals the number of directions below it. -/
theorem rank_at (I : Cell D k) (i : Fin k) :
    ((directions I).filter (fun x => x < I i)).card = i.val := by
  have h : (directions I).filter (fun x => x < I i) =
      (Finset.Iio i).map I.toEmbedding := by
    ext x
    simp only [Finset.mem_filter, mem_directions, Finset.mem_map, Finset.mem_Iio,
      RelEmbedding.coe_toEmbedding]
    constructor
    · rintro ⟨⟨j, rfl⟩, hj⟩
      exact ⟨j, I.lt_iff_lt.mp hj, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, rfl⟩, I.lt_iff_lt.mpr hj⟩
  rw [h, Finset.card_map, Fin.card_Iio]

theorem complement_rank_sum (h : k + l = D) (I : Cell D k) (x : Fin D) :
    ((directions I).filter (fun y => y < x)).card +
      ((directions (complement h I)).filter (fun y => y < x)).card = x.val := by
  have h₁ : (directions I).filter (fun y => y < x) =
      (Finset.Iio x).filter (fun y => y ∈ directions I) := by ext; simp [and_comm]
  have h₂ : (directions (complement h I)).filter (fun y => y < x) =
      (Finset.Iio x).filter (fun y => y ∉ directions I) := by ext; simp [and_comm]
  rw [h₁, h₂, Finset.card_filter_add_card_filter_not, Fin.card_Iio]

/-- A removed direction occurs in the complementary enlarged cell. -/
theorem exists_complement_face_index (h : k + 1 + l = D)
    (I : Cell D (k + 1)) (i : Fin (k + 1)) :
    ∃ b : Fin (l + 1), complement (by omega : k + (l + 1) = D) (face I i) b = I i := by
  apply (mem_directions _ _).mp
  rw [directions_complement_face h]
  exact Finset.mem_insert_self _ _

/-- The complementary deletion removes precisely the missing original direction. -/
theorem complement_face_face (h : k + 1 + l = D)
    (I : Cell D (k + 1)) (i : Fin (k + 1)) (b : Fin (l + 1))
    (hb : complement (by omega : k + (l + 1) = D) (face I i) b = I i) :
    face (complement (by omega : k + (l + 1) = D) (face I i)) b = complement h I := by
  apply directions_injective
  rw [directions_face, hb, directions_complement_face h]
  apply Finset.erase_insert
  simp only [directions_complement, Finset.mem_compl, not_not]
  exact (mem_directions I _).mpr ⟨i, rfl⟩

/-- The two deletion positions partition the directions below the removed one. -/
theorem complement_face_index_sum (h : k + 1 + l = D)
    (I : Cell D (k + 1)) (i : Fin (k + 1)) (b : Fin (l + 1))
    (hb : complement (by omega : k + (l + 1) = D) (face I i) b = I i) :
    i.val + b.val = (I i).val := by
  have hs := complement_rank_sum (by omega : k + (l + 1) = D) (face I i) (I i)
  have h₁ : ((directions (face I i)).filter (fun x => x < I i)).card = i.val := by
    have he : (directions (face I i)).filter (fun x => x < I i) =
        (directions I).filter (fun x => x < I i) := by
      rw [directions_face]
      ext x
      simp only [Finset.mem_filter, Finset.mem_erase]
      exact ⟨fun hx => ⟨hx.1.2, hx.2⟩, fun hx => ⟨⟨ne_of_lt hx.2, hx.1⟩, hx.2⟩⟩
    rw [he, rank_at]
  rw [h₁, ← hb, rank_at] at hs
  simpa only [hb] using hs

def dualIndex (h : k + 1 + l = D) (I : Cell D (k + 1)) (i : Fin (k + 1)) : Fin (l + 1) :=
  (exists_complement_face_index h I i).choose

theorem dualIndex_apply (h : k + 1 + l = D) (I : Cell D (k + 1)) (i : Fin (k + 1)) :
    complement (by omega : k + (l + 1) = D) (face I i) (dualIndex h I i) = I i :=
  (exists_complement_face_index h I i).choose_spec

theorem dualIndex_face (h : k + 1 + l = D) (I : Cell D (k + 1)) (i : Fin (k + 1)) :
    face (complement (by omega : k + (l + 1) = D) (face I i)) (dualIndex h I i) =
      complement h I :=
  complement_face_face h I i _ (dualIndex_apply h I i)

theorem incidence_reverse (h : k + 1 + l = D)
    (I : Cell D (k + 1)) (J : Cell D (l + 1)) (b : Fin (l + 1))
    (hb : face J b = complement h I) :
    ∃ a : Fin (k + 1),
      complement (by omega : k + (l + 1) = D) (face I a) = J ∧ dualIndex h I a = b := by
  let a := dualIndex (by omega : l + 1 + k = D) J b
  have hC : complement (by omega : l + (k + 1) = D) (face J b) = I := by
    rw [hb]
    exact complement_involutive h I
  have ha : I a = J b := by
    simpa only [hC] using dualIndex_apply (by omega : l + 1 + k = D) J b
  have hf : face I a = complement (by omega : l + 1 + k = D) J := by
    simpa only [hC] using dualIndex_face (by omega : l + 1 + k = D) J b
  have hJ : complement (by omega : k + (l + 1) = D) (face I a) = J := by
    rw [hf]
    exact complement_involutive (by omega : l + 1 + k = D) J
  refine ⟨a, hJ, J.injective ?_⟩
  calc
    J (dualIndex h I a) = complement (by omega : k + (l + 1) = D) (face I a)
        (dualIndex h I a) := congrArg (fun C => C (dualIndex h I a)) hJ.symm
    _ = I a := dualIndex_apply h I a
    _ = J b := ha

/-- The actual bijection between primal and complementary boundary incidences. -/
def incidenceEquiv (h : k + 1 + l = D) (I : Cell D (k + 1)) (J : Cell D (l + 1)) :
    {a : Fin (k + 1) // complement (by omega : k + (l + 1) = D) (face I a) = J} ≃
      {b : Fin (l + 1) // face J b = complement h I} :=
  Equiv.ofBijective
    (fun a => ⟨dualIndex h I a, by
      simpa only [a.property] using dualIndex_face h I a⟩)
    ⟨by
      intro a a' he
      apply Subtype.ext
      apply I.injective
      have h₁ := dualIndex_apply h I a
      have h₂ := dualIndex_apply h I a'
      rw [a.property] at h₁
      rw [a'.property] at h₂
      exact h₁.symm.trans ((congrArg J (congrArg Subtype.val he)).trans h₂),
    by
      intro b
      obtain ⟨a, ha, hb⟩ := incidence_reverse h I J b b.property
      exact ⟨⟨a, ha⟩, Subtype.ext hb⟩⟩

variable (A : Type*) [CommRing A]

/-- A degree-adjusted Hodge sign. This convention makes the transpose
differential identity have no extra degree-dependent sign. -/
def orientation (I : Cell D k) : A := (-1 : A) ^ ∑ x ∈ directions I, x.val

theorem orientation_sq (I : Cell D k) : orientation A I * orientation A I = 1 := by
  simp only [orientation, ← mul_pow, neg_mul_neg, one_mul, one_pow]

theorem orientation_face (I : Cell D (k + 1)) (i : Fin (k + 1)) :
    orientation A I = orientation A (face I i) * (-1 : A) ^ (I i).val := by
  rw [orientation, orientation, directions_face, ← pow_add,
    Finset.sum_erase_add _ _ ((mem_directions I _).mpr ⟨i, rfl⟩)]

/-- The exact signed coefficient identity for complementary incidences. -/
theorem orientation_incidence (h : k + 1 + l = D)
    (I : Cell D (k + 1)) (i : Fin (k + 1)) (b : Fin (l + 1))
    (hb : complement (by omega : k + (l + 1) = D) (face I i) b = I i) :
    (-1 : A) ^ i.val * orientation A (face I i) =
      (-1 : A) ^ b.val * orientation A I := by
  rw [orientation_face, ← complement_face_index_sum h I i b hb, pow_add]
  have hh : (-1 : A) ^ b.val * (-1 : A) ^ b.val = 1 := by
    rw [← mul_pow]
    simp
  calc
    _ = ((-1 : A) ^ b.val * (-1 : A) ^ b.val) *
        ((-1 : A) ^ i.val * orientation A (face I i)) := by rw [hh, one_mul]
    _ = _ := by ring

end
end Decoupling.HighDim.Toric.Hodge
