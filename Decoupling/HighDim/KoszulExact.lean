import Decoupling.HighDim.KoszulDecompositionDifferential

/-!
# Exactness of the actual Laurent Koszul complex

Source: `drafts/main.tex:370–382`.
The proof inducts on an injectively selected set of coordinate differences
inside the fixed Laurent ring. It uses the actual ordered-cell decomposition
and the proved partial-evaluation cancellation, constructing boundary
preimages explicitly. No exactness or regularity certificate is supplied
as an external hypothesis.
-/

namespace Decoupling.HighDim.Koszul

open CategoryTheory

noncomputable section

variable {K : Type*} [CommRing K] [IsDomain K] {D n : ℕ}

theorem selected_initial_preimage (ι : Fin (n + 1) ↪ Fin D)
    (a : Term (Laurent K D) n 1) (b : Term (Laurent K D) n 0)
    (h : (boundary (Laurent K D) (fun j => difference K (ι j.succ)) 0).hom a +
      difference K (ι 0) • b = 0) :
    ∃ c : Term (Laurent K D) n 1,
      (boundary (Laurent K D) (fun j => difference K (ι j.succ)) 0).hom c = b := by
  classical
  let T : Finset (Fin D) := Finset.univ.image (fun j : Fin n => ι j.succ)
  have hT : coordinateIdeal K T =
      Ideal.span (Set.range (fun j : Fin n => difference K (ι j.succ))) := by
    simp [coordinateIdeal, T, ← Set.range_comp, Function.comp_def]
  have hi : ι 0 ∉ T := by
    rintro hin
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hin
    exact Fin.succ_ne_zero j (ι.injective hj)
  have ha : firstBoundary (Laurent K D) (fun j => difference K (ι j.succ)) a ∈
      coordinateIdeal K T := by
    rw [hT, ← range_firstBoundary]
    exact ⟨a, rfl⟩
  have he := congrArg (zeroTermEquiv (Laurent K D)) h
  simp only [map_add, map_smul, map_zero, smul_eq_mul] at he
  have hw : difference K (ι 0) * zeroTermEquiv (Laurent K D) b ∈ coordinateIdeal K T := by
    rw [eq_neg_of_add_eq_zero_right he]
    exact (coordinateIdeal K T).neg_mem ha
  have hb := (difference_mul_mem_coordinateIdeal_iff T (ι 0) hi
    (zeroTermEquiv (Laurent K D) b)).mp hw
  rw [hT, ← range_firstBoundary] at hb
  obtain ⟨c, hc⟩ := hb
  exact ⟨c, (zeroTermEquiv (Laurent K D)).injective hc⟩

/-- Every positive-degree cycle for any injectively selected Laurent
coordinate differences is a boundary in the actual signed complex. -/
theorem selected_exact (n : ℕ) (ι : Fin n ↪ Fin D) (k : ℕ)
    (v : Term (Laurent K D) n (k + 1))
    (hv : (boundary (Laurent K D) (fun i => difference K (ι i)) k).hom v = 0) :
    ∃ z : Term (Laurent K D) n (k + 2),
      (boundary (Laurent K D) (fun i => difference K (ι i)) (k + 1)).hom z = v := by
  induction n generalizing k with
  | zero =>
    have : Subsingleton (Term (Laurent K D) 0 (k + 1)) :=
      term_subsingleton (Laurent K D) (by omega)
    exact ⟨0, by simpa only [map_zero] using (Subsingleton.elim 0 v)⟩
  | succ n ih =>
    let A := Laurent K D
    let w : Fin (n + 1) → A := fun i => difference K (ι i)
    let t : Fin n ↪ Fin D := (Fin.succEmb n).trans ι
    obtain ⟨⟨a, b⟩, rfl⟩ := (termJoinEquiv A k).surjective v
    have hc : ∃ c : Term A n (k + 1), (boundary A (fun i => w i.succ) k).hom c = b := by
      cases k with
      | zero =>
        rw [boundary_join_zero] at hv
        have he : (boundary A (fun i => w i.succ) 0).hom a + w 0 • b = 0 :=
          (liftTerm_injective A 0) (by simpa only [map_zero] using hv)
        exact selected_initial_preimage ι a b he
      | succ k =>
        rw [boundary_join] at hv
        have he : ((boundary A (fun i => w i.succ) (k + 1)).hom a + w 0 • b,
            -(boundary A (fun i => w i.succ) k).hom b) = (0, 0) :=
          (termJoinEquiv A k).injective (by
            change _ = (termJoinEquiv A k) 0
            rw [map_zero]
            exact hv)
        have hb : (boundary A (fun i => w i.succ) k).hom b = 0 := by
          have hh := congrArg Prod.snd he
          simpa only [Prod.snd_zero, neg_eq_zero] using hh
        exact ih t k b hb
    obtain ⟨c, hc⟩ := hc
    have ha : (boundary A (fun i => w i.succ) k).hom (a + w 0 • c) = 0 := by
      rw [map_add, map_smul, hc]
      cases k with
      | zero =>
        rw [boundary_join_zero] at hv
        exact (liftTerm_injective A 0) (by simpa only [map_zero] using hv)
      | succ k =>
        rw [boundary_join] at hv
        have he : ((boundary A (fun i => w i.succ) (k + 1)).hom a + w 0 • b,
            -(boundary A (fun i => w i.succ) k).hom b) = (0, 0) :=
          (termJoinEquiv A k).injective (by
            change _ = (termJoinEquiv A k) 0
            rw [map_zero]
            exact hv)
        exact congrArg Prod.fst he
    obtain ⟨x, hx⟩ := ih t k (a + w 0 • c) ha
    change (boundary A (fun i => w i.succ) (k + 1)).hom x = a + w 0 • c at hx
    refine ⟨termJoinEquiv A (k + 1) (x, -c), ?_⟩
    change (boundary A w (k + 1)).hom (termJoinEquiv A (k + 1) (x, -c)) = _
    rw [boundary_join A w k x (-c), map_neg, hx, hc]
    simp

/-- Positive-degree exactness of the complete Laurent coordinate Koszul
complex, for arbitrary dimension and any coefficient domain. -/
theorem laurent_exact (K : Type*) [CommRing K] [IsDomain K] (D k : ℕ)
    (v : Term (Laurent K D) D (k + 1))
    (hv : (boundary (Laurent K D) (difference K) k).hom v = 0) :
    ∃ z : Term (Laurent K D) D (k + 2),
      (boundary (Laurent K D) (difference K) (k + 1)).hom z = v :=
  selected_exact D (Function.Embedding.refl (Fin D)) k v hv

end

end Decoupling.HighDim.Koszul
