import Decoupling.HighDim.KoszulContractionMap

/-!
# Ordered deletion and the interior-product signs

The sign is computed by deleting the directions of `I` in increasing
order and adding their positions in the successive cells. Thus it is
exactly the usual interior-product sign, including in odd characteristic.
-/

namespace Decoupling.HighDim.KoszulContraction
open CategoryTheory Koszul TrivialLayers ExtValuesTensor Toric.Hodge
open scoped TensorProduct
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {D : ℕ}

/-- Explicit ordered deletion. `none` means that the removed cell is not
a subcell. The natural number records the sum of the deletion positions. -/
def deletion : (n : ℕ) → Cell D n → (q : ℕ) → Cell D (q + n) → Option (ℕ × Cell D q)
  | 0, _, _q, J => some (0, J)
  | n + 1, I, q, J =>
      if h : ∃ a, J a = I 0 then
        (deletion n (face I 0) q (face J h.choose)).map
          (fun x => (h.choose.val + x.1, x.2))
      else none

/-- Exactly the subsets of the input cell survive ordered contraction. -/
theorem deletion_ne_none_iff : ∀ (n : ℕ) (I : Cell D n) (q : ℕ) (J : Cell D (q + n)),
    deletion n I q J ≠ none ↔ directions I ⊆ directions J := by
  intro n
  induction n with
  | zero =>
    intro I q J
    have hI : directions I = ∅ := Finset.card_eq_zero.mp (directions_card I)
    simp [deletion, hI]
  | succ n ih =>
    intro I q J
    by_cases h : ∃ a, J a = I 0
    · simp only [deletion, dite_eq_left h]
      have hm : ((deletion n (face I 0) q (face J h.choose)).map
          (fun x => (h.choose.val + x.1, x.2))) ≠ none ↔
          deletion n (face I 0) q (face J h.choose) ≠ none := by
        cases deletion n (face I 0) q (face J h.choose) <;> simp
      rw [hm, ih]
      rw [directions_face, directions_face]
      erw [h.choose_spec]
      have ha : I 0 ∈ directions J := (mem_directions J _).mpr h
      constructor
      · intro hs x hx
        by_cases hx0 : x = I 0
        · exact hx0 ▸ ha
        · exact Finset.mem_of_mem_erase (hs (Finset.mem_erase.mpr ⟨hx0, hx⟩))
      · intro hs x hx
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1,
          hs (Finset.mem_of_mem_erase hx)⟩
    · simp only [deletion, dite_eq_right h, ne_eq, not_true_eq_false, false_iff]
      intro hs
      exact h ((mem_directions J _).mp (hs ((mem_directions I _).mpr ⟨0, rfl⟩)))

/-- The surviving output cell is literally the set difference `J \ I`. -/
theorem deletion_directions : ∀ (n : ℕ) (I : Cell D n) (q : ℕ) (J : Cell D (q + n))
    (s : ℕ) (L : Cell D q), deletion n I q J = some (s, L) →
      directions L = directions J \ directions I := by
  intro n
  induction n with
  | zero =>
    intro I q J s L h
    have hJL : J = L := by
      change some (0, J) = some (s, L) at h
      exact congrArg Prod.snd (Option.some.inj h)
    subst L
    have hI : directions I = ∅ := Finset.card_eq_zero.mp (directions_card I)
    simp [hI]
  | succ n ih =>
    intro I q J s L he
    by_cases h : ∃ a, J a = I 0
    · simp only [deletion, dite_eq_left h, Option.map_eq_some_iff] at he
      obtain ⟨⟨t, L'⟩, ht, he⟩ := he
      have hL : L' = L := congrArg Prod.snd he
      subst L'
      rw [ih _ _ _ _ _ ht, directions_face, directions_face]
      erw [h.choose_spec]
      ext x
      have ha : I 0 ∈ directions I := (mem_directions I _).mpr ⟨0, rfl⟩
      by_cases hx : x = I 0
      · subst x; simp [ha]
      · simp only [Finset.mem_sdiff, Finset.mem_erase]
        tauto
    · simp only [deletion, dite_eq_right h] at he
      cases he

/-- The ordered normalization has sign +1 on its own top cell. -/
theorem deletion_equal_directions : ∀ (n : ℕ) (I : Cell D n) (J : Cell D (0 + n)),
    directions I = directions J → deletion n I 0 J = some (0, zeroCell D) := by
  intro n
  induction n with
  | zero =>
    intro I J _
    have hJ : J = zeroCell D := by
      apply DFunLike.ext
      intro a
      exact Fin.elim0 a
    simp only [deletion, hJ]
  | succ n ih =>
    intro I J he
    have h : ∃ a, J a = I 0 := (mem_directions J _).mp
      (he ▸ (mem_directions I _).mpr ⟨0, rfl⟩)
    have ha : h.choose.val = 0 := by
      rw [← rank_at J h.choose, h.choose_spec, ← he, rank_at I 0]
      rfl
    have hf : directions (face I 0) = directions (face J h.choose) := by
      rw [directions_face, directions_face]
      erw [h.choose_spec]
      rw [he]
    simp only [deletion, dite_eq_left h, ih _ _ hf, Option.map_some, ha, zero_add]

/-- The complement and the explicit interior-product sign exponent for
an actual subcell. Existence is proved by ordered deletion. -/
def subcellData (n : ℕ) (I : Cell D n) (q : ℕ) (J : Cell D (q + n))
    (h : directions I ⊆ directions J) : ℕ × Cell D q :=
  (Option.ne_none_iff_exists'.mp ((deletion_ne_none_iff n I q J).mpr h)).choose

theorem deletion_eq_subcellData (n : ℕ) (I : Cell D n) (q : ℕ) (J : Cell D (q + n))
    (h : directions I ⊆ directions J) :
    deletion n I q J = some (subcellData n I q J h) :=
  (Option.ne_none_iff_exists'.mp ((deletion_ne_none_iff n I q J).mpr h)).choose_spec

theorem subcellData_directions (n : ℕ) (I : Cell D n) (q : ℕ) (J : Cell D (q + n))
    (h : directions I ⊆ directions J) :
    directions (subcellData n I q J h).2 = directions J \ directions I :=
  deletion_directions n I q J _ _ (deletion_eq_subcellData n I q J h)

variable {K : Type} [Field K]
  (B : ModuleCat (Laurent K D)) [FiniteDimensional K (Layers.coefficients B)]
  (hB : AugmentationAction B)

def deletionValue {q : ℕ} (r : Option (ℕ × Cell D q)) (b : Layers.coefficients B) :
    TensorTerm B q := match r with
  | none => 0
  | some (s, J) => Finsupp.single J ((-1 : Laurent K D) ^ s) ⊗ₜ[K] b

theorem direction_single_of_not_mem {q : ℕ} (J : Cell D (q + 1)) (a : Fin D)
    (h : ¬ ∃ i, J i = a) (b : Layers.coefficients B) :
    direction B a q (Finsupp.single J 1 ⊗ₜ[K] b) = 0 := by
  rw [direction_tmul, boundary_basis]
  have hz : (∑ i : Fin (q + 1),
      Finsupp.single (face J i) ((-1 : Laurent K D) ^ i.val * ((Pi.single a (1 : Laurent K D)) : Fin D → Laurent K D) (J i))) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hi : J i ≠ a := fun hi => h ⟨i, hi⟩
    simp [Pi.single_eq_of_ne hi]
  change (∑ i : Fin (q + 1),
    Finsupp.single (face J i) ((-1 : Laurent K D) ^ i.val * ((Pi.single a (1 : Laurent K D)) : Fin D → Laurent K D) (J i))) ⊗ₜ[K] b = 0
  rw [hz, TensorProduct.zero_tmul]

theorem direction_single {q : ℕ} (J : Cell D (q + 1)) (a : Fin (q + 1))
    (b : Layers.coefficients B) :
    direction B (J a) q (Finsupp.single J 1 ⊗ₜ[K] b) =
      Finsupp.single (face J a) ((-1 : Laurent K D) ^ a.val) ⊗ₜ[K] b := by
  rw [direction_tmul, YonedaDetection.coordinate_contraction_basis]

omit [FiniteDimensional K (Layers.coefficients B)] in
theorem deletionValue_map (q s : ℕ) (r : Option (ℕ × Cell D q))
    (b : Layers.coefficients B) :
    deletionValue B (r.map (fun x => (s + x.1, x.2))) b =
      ((-1 : Laurent K D) ^ s) • deletionValue B r b := by
  cases r with
  | none => simp [deletionValue]
  | some x =>
    rcases x with ⟨t, J⟩
    simp only [Option.map_some, deletionValue, pow_add, TensorProduct.smul_tmul',
      Finsupp.smul_single, smul_eq_mul]

/-- Exact evaluation of each genuine iterated contraction on a unit cell. -/
theorem cellComponent_single : ∀ (n : ℕ) (I : Cell D n) (q : ℕ)
    (J : Cell D (q + n)) (b : Layers.coefficients B),
    cellComponent B hB I q (Finsupp.single J 1 ⊗ₜ[K] b) =
      deletionValue B (deletion n I q J) b := by
  intro n
  induction n with
  | zero =>
    intro I q J b
    rw [cellComponent_zero]
    rfl
  | succ n ih =>
    intro I q J b
    rw [cellComponent_succ]
    change cellComponent B hB (face I 0) q
      (direction B (I 0) (q + n) (Finsupp.single J 1 ⊗ₜ[K] b)) = _
    by_cases h : ∃ a, J a = I 0
    · erw [← h.choose_spec, direction_single]
      have hv : Finsupp.single (face J h.choose) ((-1 : Laurent K D) ^ h.choose.val) ⊗ₜ[K] b =
          ((-1 : Laurent K D) ^ h.choose.val) •
            (Finsupp.single (face J h.choose) 1 ⊗ₜ[K] b) := by
        rw [TensorProduct.smul_tmul']
        simp
      rw [hv, (cellComponent B hB (face I 0) q).hom.map_smul, ih]
      simp only [deletion, dite_eq_left h]
      exact (deletionValue_map B q h.choose.val _ b).symm
    · erw [direction_single_of_not_mem B J (I 0) h b, map_zero]
      simp only [deletion, dite_eq_right h, deletionValue]

end
end Decoupling.HighDim.KoszulContraction
