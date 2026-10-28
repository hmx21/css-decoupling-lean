import Decoupling.HighDim.SchreyerModule
import Mathlib.Data.Prod.Lex

/-! # Module monomial orders and actual leading terms
The hypotheses are the ordinary order axioms, never Gröbner or resolution
properties. Nonzero vectors have a unique maximal supported module term.
-/
namespace Decoupling.HighDim.SchreyerModule
noncomputable section

structure ModuleOrder (D r : ℕ) where
  scalarOrder : MonomialOrder (Fin D)
  termOrder : LinearOrder (Term D r)
  wellFounded : WellFounded termOrder.lt
  shift_lt : ∀ a s t, termOrder.lt s t → termOrder.lt (shift a s) (shift a t)
  scalar_lt : ∀ (a b : Exponent D) (i : Fin r),
    scalarOrder.toSyn a < scalarOrder.toSyn b → termOrder.lt (a,i) (b,i)

namespace ModuleOrder
variable {D r : ℕ} (o : ModuleOrder D r)
def LE (s t : Term D r) : Prop := @LE.le _ o.termOrder.toLE s t
def LT (s t : Term D r) : Prop := @LT.lt _ o.termOrder.toLT s t

theorem le_refl (s : Term D r) : o.LE s s := @_root_.le_refl _ o.termOrder.toPreorder s
theorem le_trans {s t u : Term D r} (h : o.LE s t) (g : o.LE t u) : o.LE s u :=
  @_root_.le_trans _ o.termOrder.toPreorder _ _ _ h g
theorem lt_of_le_of_ne {s t : Term D r} (h : o.LE s t) (hn : s≠t) : o.LT s t := by
  let _ := o.termOrder
  exact @_root_.lt_of_le_of_ne _ o.termOrder.toPartialOrder _ _ h hn

theorem le_shift (a : Exponent D) (t : Term D r) : o.LE t (shift a t) := by
  let _ := o.termOrder
  by_cases ha : a=0
  · simp only [ha,shift_zero]
    exact o.le_refl t
  · apply @_root_.le_of_lt _ o.termOrder.toPreorder
    apply o.scalar_lt
    rw [map_add]
    have hp : 0 < o.scalarOrder.toSyn a := by
      apply o.scalarOrder.toSyn_lt_iff_ne_zero.mpr
      exact fun he => ha (o.scalarOrder.toSyn.injective (he.trans (map_zero _).symm))
    exact lt_add_of_pos_left _ hp

theorem shift_le (a : Exponent D) {s t : Term D r} (h : o.LE s t) :
    o.LE (shift a s) (shift a t) := by
  let _ := o.termOrder
  rcases (@eq_or_lt_of_le _ o.termOrder.toPartialOrder _ _ h) with he|hl
  · exact @_root_.le_of_eq _ o.termOrder.toPreorder _ _ (congrArg (shift a) he)
  · exact @_root_.le_of_lt _ o.termOrder.toPreorder _ _ (o.shift_lt a s t hl)
end ModuleOrder

variable {K : Type*} [CommRing K] {D r : ℕ}

def Bounded (o : ModuleOrder D r) (f : Vec K D r) (t : Term D r) : Prop :=
  ∀ u, coeff f u≠0 → o.LE u t

def StrictlyBelow (o : ModuleOrder D r) (f : Vec K D r) (t : Term D r) : Prop :=
  ∀ u, coeff f u≠0 → o.LT u t

def IsLeading (o : ModuleOrder D r) (f : Vec K D r) (t : Term D r) : Prop :=
  coeff f t≠0 ∧ Bounded o f t

def lm (o : ModuleOrder D r) (f : Vec K D r) (hf : f≠0) : Term D r := by
  let _ := o.termOrder
  exact (support f).max' ((support_nonempty_iff f).mpr hf)

def lc (o : ModuleOrder D r) (f : Vec K D r) (hf : f≠0) : K := coeff f (lm o f hf)

theorem lm_mem (o : ModuleOrder D r) (f : Vec K D r) (hf : f≠0) : lm o f hf ∈ support f := by
  let _ := o.termOrder
  exact Finset.max'_mem _ _

theorem lc_ne_zero (o : ModuleOrder D r) (f : Vec K D r) (hf : f≠0) : lc o f hf≠0 :=
  (mem_support f _).mp (lm_mem o f hf)

theorem lm_isLeading (o : ModuleOrder D r) (f : Vec K D r) (hf : f≠0) : IsLeading o f (lm o f hf) := by
  let _ := o.termOrder
  refine ⟨lc_ne_zero o f hf,?_⟩
  intro u hu
  exact Finset.le_max' _ _ ((mem_support f u).mpr hu)

theorem isLeading_unique (o : ModuleOrder D r) {f : Vec K D r} {s t : Term D r}
    (hs : IsLeading o f s) (ht : IsLeading o f t) : s=t := by
  let _ := o.termOrder
  exact @le_antisymm _ o.termOrder.toPartialOrder _ _ (ht.2 s hs.1) (hs.2 t ht.1)

theorem IsLeading.ne_zero {o : ModuleOrder D r} {f : Vec K D r} {t : Term D r}
    (hf : IsLeading o f t) : f≠0 := by
  intro he
  exact hf.1 (by simp [he])

theorem isLeading_lm (o : ModuleOrder D r) {f : Vec K D r} {t : Term D r}
    (hf : IsLeading o f t) : lm o f hf.ne_zero=t :=
  isLeading_unique o (lm_isLeading o f hf.ne_zero) hf

theorem bounded_mono {o : ModuleOrder D r} {f : Vec K D r} {s t : Term D r}
    (hf : Bounded o f s) (hst : o.LE s t) : Bounded o f t :=
  fun u hu => o.le_trans (hf u hu) hst

theorem below_of_bounded_of_lt {o : ModuleOrder D r} {f : Vec K D r} {s t : Term D r}
    (hf : Bounded o f s) (hst : o.LT s t) : StrictlyBelow o f t := by
  let _ := o.termOrder
  exact fun u hu => @lt_of_le_of_lt _ o.termOrder.toPreorder _ _ _ (hf u hu) hst

theorem bounded_of_below {o : ModuleOrder D r} {f : Vec K D r} {t : Term D r}
    (hf : StrictlyBelow o f t) : Bounded o f t := by
  let _ := o.termOrder
  exact fun u hu => @le_of_lt _ o.termOrder.toPreorder _ _ (hf u hu)

theorem below_iff_lm_lt (o : ModuleOrder D r) (f : Vec K D r) (hf : f≠0) (t : Term D r) :
    StrictlyBelow o f t ↔ o.LT (lm o f hf) t := by
  constructor
  · exact fun h => h _ (lc_ne_zero o f hf)
  · exact below_of_bounded_of_lt (lm_isLeading o f hf).2

@[simp] theorem bounded_zero (o : ModuleOrder D r) (t : Term D r) : Bounded o (0 : Vec K D r) t := by
  intro u hu
  exact False.elim (hu (coeff_zero u))
@[simp] theorem below_zero (o : ModuleOrder D r) (t : Term D r) : StrictlyBelow o (0 : Vec K D r) t := by
  intro u hu
  exact False.elim (hu (coeff_zero u))

end
end Decoupling.HighDim.SchreyerModule
