import Decoupling.HighDim.KoszulDecomposition

/-!
# Differential formulas in the actual first-coordinate decomposition

The signed formulas are proved on the ordered-cell basis. In positive
degrees they are precisely `d(a,b) = (d_tail a + w_0 b, -d_tail b)`.
-/

namespace Decoupling.HighDim.Koszul

open CategoryTheory

noncomputable section

variable {D k : ℕ}

@[simp] theorem face_liftCell (I : Cell D (k + 1)) (i : Fin (k + 1)) :
    face (liftCell I) i = liftCell (face I i) := rfl

@[simp] theorem face_prependCell_zero (I : Cell D k) :
    face (prependCell I) 0 = liftCell I := by
  apply DFunLike.ext
  intro j
  rfl

@[simp] theorem face_prependCell_succ (I : Cell D (k + 1)) (i : Fin (k + 1)) :
    face (prependCell I) i.succ = prependCell (face I i) := by
  apply DFunLike.ext
  intro j
  cases j using Fin.cases with
  | zero => simp [face_apply]
  | succ j => simp [face_apply, Fin.succ_succAbove_succ]

variable (A : Type*) [CommRing A] (w : Fin (D + 1) → A)

theorem boundary_lift (k : ℕ) (a : Term A D (k + 1)) :
    (boundary A w k).hom (liftTerm A (k + 1) a) =
      liftTerm A k ((boundary A (fun i => w i.succ) k).hom a) := by
  have hl : (boundary A w k).hom.comp (liftTerm A (k + 1)) =
      (liftTerm A k).comp (boundary A (fun i => w i.succ) k).hom := by
    apply (Finsupp.basisSingleOne : Module.Basis (Cell D (k + 1)) A (Term A D (k + 1))).ext
    intro I
    change (boundary A w k).hom (liftTerm A (k + 1) (Finsupp.single I 1)) =
      liftTerm A k ((boundary A (fun i => w i.succ) k).hom (Finsupp.single I 1))
    simp only [liftTerm_single]
    change boundary A w k (Finsupp.single (liftCell I) 1) =
      liftTerm A k (boundary A (fun i => w i.succ) k (Finsupp.single I 1))
    rw [boundary_basis, boundary_basis, map_sum]
    simp only [face_liftCell, liftCell_apply, liftTerm_single]
  exact DFunLike.congr_fun hl a

theorem boundary_prepend (k : ℕ) (b : Term A D (k + 1)) :
    (boundary A w (k + 1)).hom (prependTerm A (k + 1) b) =
      liftTerm A (k + 1) (w 0 • b) -
        prependTerm A k ((boundary A (fun i => w i.succ) k).hom b) := by
  have hl : (boundary A w (k + 1)).hom.comp (prependTerm A (k + 1)) =
      w 0 • liftTerm A (k + 1) -
        (prependTerm A k).comp (boundary A (fun i => w i.succ) k).hom := by
    apply (Finsupp.basisSingleOne : Module.Basis (Cell D (k + 1)) A (Term A D (k + 1))).ext
    intro I
    change (boundary A w (k + 1)).hom (prependTerm A (k + 1) (Finsupp.single I 1)) =
      w 0 • liftTerm A (k + 1) (Finsupp.single I 1) -
        prependTerm A k ((boundary A (fun i => w i.succ) k).hom (Finsupp.single I 1))
    simp only [prependTerm_single, liftTerm_single]
    change boundary A w (k + 1) (Finsupp.single (prependCell I) 1) =
      w 0 • Finsupp.single (liftCell I) 1 -
        prependTerm A k (boundary A (fun i => w i.succ) k (Finsupp.single I 1))
    rw [boundary_basis, boundary_basis, map_sum, Fin.sum_univ_succ]
    simp [pow_succ, Finsupp.smul_single, smul_eq_mul, sub_eq_add_neg,
      ← Finset.sum_neg_distrib]
  simpa only [LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.comp_apply,
    map_smul] using DFunLike.congr_fun hl b

theorem boundary_prepend_zero (b : Term A D 0) :
    (boundary A w 0).hom (prependTerm A 0 b) = liftTerm A 0 (w 0 • b) := by
  have hl : (boundary A w 0).hom.comp (prependTerm A 0) = w 0 • liftTerm A 0 := by
    apply (Finsupp.basisSingleOne : Module.Basis (Cell D 0) A (Term A D 0)).ext
    intro I
    change boundary A w 0 (prependTerm A 0 (Finsupp.single I 1)) =
      w 0 • liftTerm A 0 (Finsupp.single I 1)
    rw [prependTerm_single, boundary_basis]
    simp [Finsupp.smul_single, smul_eq_mul]
  simpa only [LinearMap.comp_apply, LinearMap.smul_apply, map_smul] using
    DFunLike.congr_fun hl b

/-- This equality is the concrete cone differential, with its minus sign. -/
theorem boundary_join (k : ℕ) (a : Term A D (k + 2)) (b : Term A D (k + 1)) :
    (boundary A w (k + 1)).hom (termJoinEquiv A (k + 1) (a, b)) =
      termJoinEquiv A k
        ((boundary A (fun i => w i.succ) (k + 1)).hom a + w 0 • b,
          -(boundary A (fun i => w i.succ) k).hom b) := by
  rw [termJoinEquiv_apply, map_add, boundary_lift A w (k + 1) a,
    boundary_prepend A w k b, termJoinEquiv_apply, map_add, map_neg]
  abel

theorem boundary_join_zero (a : Term A D 1) (b : Term A D 0) :
    (boundary A w 0).hom (termJoinEquiv A 0 (a, b)) =
      liftTerm A 0 ((boundary A (fun i => w i.succ) 0).hom a + w 0 • b) := by
  rw [termJoinEquiv_apply, map_add, boundary_lift A w 0 a,
    boundary_prepend_zero A w b, map_add]

theorem liftTerm_injective (k : ℕ) : Function.Injective (liftTerm A (D := D) k) :=
  Finsupp.mapDomain_injective liftCell_injective

end

end Decoupling.HighDim.Koszul
