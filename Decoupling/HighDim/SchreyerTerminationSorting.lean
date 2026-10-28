import Decoupling.HighDim.SchreyerTerminationExponent
import Decoupling.HighDim.SchreyerGroebnerDivision
import Mathlib.Data.Finset.Sort

/-! # Reindexing minimal leading families in descending lexicographic order
The construction permutes existing generators and preserves their actual
submodule and minimal Gröbner property. It chooses no module basis.
-/
namespace Decoupling.HighDim.SchreyerTermination
open SchreyerModule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D r s : ℕ}

theorem lexGE_iff_toLex_le (a b : Exponent D) : LexGE a b ↔ toLex b ≤ toLex a := by
  constructor
  · rintro (rfl | ⟨i,hp,hi⟩)
    · exact le_rfl
    · exact le_of_lt ⟨i,fun j hj => (hp j hj).symm,hi⟩
  · intro h
    rcases eq_or_lt_of_le h with he | hl
    · exact Or.inl (congrArg ofLex he).symm
    · rcases hl with ⟨i,hp,hi⟩
      exact Or.inr ⟨i,fun j hj => (hp j hj).symm,hi⟩

def sortKey (t : Fin s → Term D r) (i : Fin s) : Fin r ×ₗ (Lex (Exponent D))ᵒᵈ :=
  toLex ((t i).2,toLex (t i).1)

theorem sortKey_injective (t : Fin s → Term D r) (ht : Function.Injective t) :
    Function.Injective (sortKey t) := by
  intro i j he
  have hp := congrArg Prod.fst (congrArg ofLex he)
  have hx := congrArg ofLex (congrArg Prod.snd (congrArg ofLex he))
  exact ht (Prod.ext hx hp)

structure SortingIndex (s : ℕ) where
  val : Fin s

def sortingIndexEquiv : SortingIndex s ≃ Fin s where
  toFun := SortingIndex.val
  invFun i := ⟨i⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (SortingIndex s) := Fintype.ofEquiv (Fin s) sortingIndexEquiv.symm

/-- A reindexing of the given finite family, with the required within-position
lexicographic order. No assumption about its lower polynomial terms occurs. -/
theorem exists_sorted_reindex (t : Fin s → Term D r) (ht : Function.Injective t) :
    ∃ p : Equiv.Perm (Fin s), ∀ i j, i<j → (t (p i)).2=(t (p j)).2 →
      LexGE (t (p i)).1 (t (p j)).1 := by
  classical
  let : LinearOrder (SortingIndex s) := LinearOrder.lift' (fun i : SortingIndex s => sortKey t i.val)
    ((sortKey_injective t ht).comp sortingIndexEquiv.injective)
  have hcard : Fintype.card (SortingIndex s)=s :=
    (Fintype.card_congr sortingIndexEquiv).trans (Fintype.card_fin s)
  let e := Fintype.orderIsoFinOfCardEq (SortingIndex s) hcard
  let p : Equiv.Perm (Fin s) := e.toEquiv.trans sortingIndexEquiv
  refine ⟨p,?_⟩
  intro i j hij hpos
  have he : sortKey t (p i) ≤ sortKey t (p j) := e.monotone hij.le
  dsimp only [sortKey] at he
  rcases Prod.Lex.toLex_le_toLex.mp he with hp | hp
  · exact False.elim ((ne_of_lt hp) hpos)
  · exact (lexGE_iff_toLex_le _ _).mpr hp.2

variable {K : Type*} [Field K] {o : ModuleOrder D r}
  {G : Fin s → Vec K D r} {N : Submodule (Poly K D) (Vec K D r)}

theorem leading_injective_of_minimal (hG : IsMinimal o G) (t : Fin s → Term D r)
    (hlead : ∀ i, IsLeading o (G i) (t i)) : Function.Injective t := by
  intro i j he
  exact hG.minimal i j (t i) (t j) (hlead i) (hlead j)
    ⟨congrArg Prod.snd he,le_of_eq (congrArg Prod.fst he)⟩

theorem groebner_reindex (hG : IsGroebnerBasis o G N) (p : Equiv.Perm (Fin s)) :
    IsGroebnerBasis o (fun i => G (p i)) N := by
  refine ⟨fun i => hG.mem (p i),?_⟩
  intro f hf t ht
  obtain ⟨i,u,hi,hu⟩ := hG.leading f hf t ht
  refine ⟨p.symm i,u,?_,hu⟩
  simpa only [Equiv.apply_symm_apply] using hi

theorem minimal_reindex (hG : IsMinimal o G) (p : Equiv.Perm (Fin s)) :
    IsMinimal o (fun i => G (p i)) := by
  refine ⟨fun i => hG.nonzero (p i),?_⟩
  intro i j u v hi hj hdiv
  exact p.injective (hG.minimal (p i) (p j) u v hi hj hdiv)

/-- The sorted minimal Gröbner family exists for the actual submodule. -/
theorem exists_sorted_minimal_groebner (o : ModuleOrder D r)
    (N : Submodule (Poly K D) (Vec K D r)) :
    ∃ s : ℕ, ∃ G : Fin s → Vec K D r, ∃ t : Fin s → Term D r,
      IsGroebnerBasis o G N ∧ IsMinimal o G ∧ (∀ i,IsLeading o (G i) (t i)) ∧
      (∀ i j,i<j → (t i).2=(t j).2 → LexGE (t i).1 (t j).1) := by
  obtain ⟨s,G,hG,hmin⟩ := exists_minimal_groebner o N
  let t : Fin s → Term D r := fun i => lm o (G i) (hmin.nonzero i)
  have hlead : ∀ i, IsLeading o (G i) (t i) := fun i => lm_isLeading o (G i) (hmin.nonzero i)
  obtain ⟨p,hp⟩ := exists_sorted_reindex t (leading_injective_of_minimal hmin t hlead)
  exact ⟨s,fun i => G (p i),fun i => t (p i),groebner_reindex hG p,minimal_reindex hmin p,
    fun i => hlead (p i),hp⟩

end
end Decoupling.HighDim.SchreyerTermination
