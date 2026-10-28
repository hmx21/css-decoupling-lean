import Decoupling.HighDim.KoszulAugmentation
import Mathlib.Order.Fin.Tuple
import Mathlib.LinearAlgebra.Finsupp.SumProd

/-!
# The first-coordinate decomposition of the ordered-cell Koszul complex

The maps here act on the same ordered embeddings used by `Koszul.complex`.
They separate cells containing direction zero from cells not containing it.
This supplies the concrete coordinate decomposition for the exactness
induction; there is no abstract exactness field or supplied cone certificate.
-/

namespace Decoupling.HighDim.Koszul

open CategoryTheory

noncomputable section

variable {D k : ℕ}

/-- Shift all directions by one; the resulting cell omits direction zero. -/
def liftCell (I : Cell D k) : Cell (D + 1) k := I.trans (Fin.succOrderEmb D)

@[simp] theorem liftCell_apply (I : Cell D k) (j : Fin k) : liftCell I j = (I j).succ := rfl

/-- Insert direction zero at the beginning of the increasing list. -/
def prependCell (I : Cell D k) : Cell (D + 1) (k + 1) :=
  OrderEmbedding.ofStrictMono (Fin.cons 0 (fun j => (I j).succ))
    (Fin.strictMono_cons.mpr ⟨fun _ => Fin.succ_pos _, Fin.strictMono_succ.comp I.strictMono⟩)

@[simp] theorem prependCell_zero (I : Cell D k) : prependCell I 0 = 0 := rfl
@[simp] theorem prependCell_succ (I : Cell D k) (j : Fin k) :
    prependCell I j.succ = (I j).succ := rfl

theorem liftCell_injective : Function.Injective (liftCell : Cell D k → Cell (D + 1) k) := by
  intro I J h
  apply DFunLike.ext
  intro j
  exact Fin.succ_injective D (DFunLike.congr_fun h j)

theorem prependCell_injective :
    Function.Injective (prependCell : Cell D k → Cell (D + 1) (k + 1)) := by
  intro I J h
  apply DFunLike.ext
  intro j
  exact Fin.succ_injective D (DFunLike.congr_fun h j.succ)

def lowerCell (I : Cell (D + 1) (k + 1)) (h : I 0 ≠ 0) : Cell D (k + 1) := by
  have hn : ∀ j, I j ≠ 0 := by
    intro j hj
    have hz := I.monotone (Fin.zero_le j)
    rw [hj] at hz
    exact h (le_antisymm hz (Fin.zero_le _))
  exact OrderEmbedding.ofStrictMono (fun j => (I j).pred (hn j))
    (Fin.strictMono_pred_comp hn I.strictMono)

def tailCell (I : Cell (D + 1) (k + 1)) : Cell D k := by
  have hn : ∀ j : Fin k, I j.succ ≠ 0 := by
    intro j
    exact Fin.ne_zero_of_lt (I.strictMono (Fin.succ_pos j))
  exact OrderEmbedding.ofStrictMono (fun j => (I j.succ).pred (hn j))
    (Fin.strictMono_pred_comp hn (I.strictMono.comp Fin.strictMono_succ))

theorem lift_lowerCell (I : Cell (D + 1) (k + 1)) (h : I 0 ≠ 0) :
    liftCell (lowerCell I h) = I := by
  apply DFunLike.ext
  intro j
  simp [liftCell, lowerCell]

theorem prepend_tailCell (I : Cell (D + 1) (k + 1)) (h : I 0 = 0) :
    prependCell (tailCell I) = I := by
  apply DFunLike.ext
  intro j
  cases j using Fin.cases with
  | zero => exact h.symm
  | succ j => simp [prependCell, tailCell]

/-- A cell either omits the first direction or contains it, uniquely. -/
def cellJoinEquiv : Cell D (k + 1) ⊕ Cell D k ≃ Cell (D + 1) (k + 1) :=
  Equiv.ofBijective (Sum.elim liftCell prependCell) (by
    constructor
    · intro x y h
      cases x with
      | inl I =>
        cases y with
        | inl J => exact congrArg Sum.inl (liftCell_injective h)
        | inr J =>
          have hh := DFunLike.congr_fun h 0
          exact False.elim (Fin.succ_ne_zero (I 0) hh)
      | inr I =>
        cases y with
        | inl J =>
          have hh := DFunLike.congr_fun h 0
          exact False.elim (Fin.succ_ne_zero (J 0) hh.symm)
        | inr J => exact congrArg Sum.inr (prependCell_injective h)
    · intro I
      by_cases h : I 0 = 0
      · exact ⟨Sum.inr (tailCell I), prepend_tailCell I h⟩
      · exact ⟨Sum.inl (lowerCell I h), lift_lowerCell I h⟩)

@[simp] theorem cellJoinEquiv_inl (I : Cell D (k + 1)) :
    cellJoinEquiv (Sum.inl I) = liftCell I := rfl

@[simp] theorem cellJoinEquiv_inr (I : Cell D k) :
    cellJoinEquiv (Sum.inr I) = prependCell I := rfl

variable (A : Type*) [CommRing A]

def liftTerm (k : ℕ) : Term A D k →ₗ[A] Term A (D + 1) k :=
  Finsupp.lmapDomain A A liftCell

def prependTerm (k : ℕ) : Term A D k →ₗ[A] Term A (D + 1) (k + 1) :=
  Finsupp.lmapDomain A A prependCell

@[simp] theorem liftTerm_single (I : Cell D k) (a : A) :
    liftTerm A k (Finsupp.single I a) = Finsupp.single (liftCell I) a := by
  simp [liftTerm]

@[simp] theorem prependTerm_single (I : Cell D k) (a : A) :
    prependTerm A k (Finsupp.single I a) = Finsupp.single (prependCell I) a := by
  simp [prependTerm]

/-- The actual finite free module decomposition induced by the cell partition. -/
def termJoinEquiv (k : ℕ) :
    (Term A D (k + 1) × Term A D k) ≃ₗ[A] Term A (D + 1) (k + 1) :=
  (Finsupp.sumFinsuppLEquivProdFinsupp A).symm.trans (Finsupp.domLCongr cellJoinEquiv)

theorem termJoinEquiv_inl_single (I : Cell D (k + 1)) (a : A) :
    termJoinEquiv A k (Finsupp.single I a, 0) = Finsupp.single (liftCell I) a := by
  have hs : (Finsupp.sumFinsuppLEquivProdFinsupp A).symm (Finsupp.single I a, 0) =
      Finsupp.single (Sum.inl I : Cell D (k + 1) ⊕ Cell D k) a := by
    ext J
    cases J <;> simp
  simp only [termJoinEquiv, LinearEquiv.trans_apply, hs, Finsupp.domLCongr_single,
    cellJoinEquiv_inl]

theorem termJoinEquiv_inr_single (I : Cell D k) (a : A) :
    termJoinEquiv A k (0, Finsupp.single I a) = Finsupp.single (prependCell I) a := by
  have hs : (Finsupp.sumFinsuppLEquivProdFinsupp A).symm (0, Finsupp.single I a) =
      Finsupp.single (Sum.inr I : Cell D (k + 1) ⊕ Cell D k) a := by
    ext J
    cases J <;> simp
  simp only [termJoinEquiv, LinearEquiv.trans_apply, hs, Finsupp.domLCongr_single,
    cellJoinEquiv_inr]

theorem termJoinEquiv_apply (a : Term A D (k + 1)) (b : Term A D k) :
    termJoinEquiv A k (a, b) = liftTerm A (k + 1) a + prependTerm A k b := by
  have hl : (termJoinEquiv A (D := D) k).toLinearMap.comp (LinearMap.inl A _ _) =
      liftTerm A (k + 1) := by
    apply Finsupp.lhom_ext
    intro I a
    simpa only [LinearMap.comp_apply, LinearMap.inl_apply, LinearEquiv.coe_coe,
      liftTerm_single] using termJoinEquiv_inl_single A I a
  have hr : (termJoinEquiv A (D := D) k).toLinearMap.comp (LinearMap.inr A _ _) =
      prependTerm A k := by
    apply Finsupp.lhom_ext
    intro I a
    simpa only [LinearMap.comp_apply, LinearMap.inr_apply, LinearEquiv.coe_coe,
      prependTerm_single] using termJoinEquiv_inr_single A I a
  have hp : (a, b) = (a, 0) + (0, b) := by simp
  rw [hp, map_add]
  exact congrArg₂ (· + ·) (DFunLike.congr_fun hl a) (DFunLike.congr_fun hr b)

end

end Decoupling.HighDim.Koszul
