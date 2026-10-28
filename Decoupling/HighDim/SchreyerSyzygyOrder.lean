import Decoupling.HighDim.SchreyerModuleLex

/-!
# The actual induced Schreyer order

A source monomial is ordered by the leading term of its image; ties put
an earlier generator index first (larger). The weighted key is injective,
and its lexicographic order is well founded. These facts hold for arbitrary
finite families, without homogeneity or an infinite base field.
-/
namespace Decoupling.HighDim.SchreyerSyzygy
open SchreyerModule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D r s : ℕ}

def weight (t : Fin s → Term D r) (u : Term D s) : Term D r :=
  shift u.1 (t u.2)

/-- An order synonym prevents the default product order on Term from
being silently selected instead of the given module order. -/
structure OrderedTerm (o : ModuleOrder D r) where
  val : Term D r

instance orderedTermOrder (o : ModuleOrder D r) : LinearOrder (OrderedTerm o) :=
  @LinearOrder.lift' _ _ o.termOrder OrderedTerm.val (by
    intro a b h
    cases a
    cases b
    cases h
    rfl)

instance orderedTermWellFounded (o : ModuleOrder D r) : WellFoundedLT (OrderedTerm o) :=
  InvImage.wf OrderedTerm.val o.wellFounded

def key (o : ModuleOrder D r) (t : Fin s → Term D r) (u : Term D s) :
    (OrderedTerm o) ×ₗ (Fin s)ᵒᵈ := toLex (⟨weight t u⟩,u.2)

theorem key_injective (o : ModuleOrder D r) (t : Fin s → Term D r) :
    Function.Injective (key o t) := by
  rintro ⟨a,i⟩ ⟨b,j⟩ h
  have he := congrArg ofLex h
  have hij : i=j := congrArg Prod.snd he
  subst j
  have hweight : shift a (t i)=shift b (t i) :=
    congrArg OrderedTerm.val (congrArg Prod.fst he)
  have hab : a=b := add_right_cancel (congrArg Prod.fst hweight)
  subst b
  rfl

@[simp] theorem weight_shift (t : Fin s → Term D r) (a : Exponent D) (u : Term D s) :
    weight t (shift a u)=shift a (weight t u) := by
  simp only [weight,shift,add_assoc]

/-- The reverse finite-index tie rule is part of the constructed order. -/
def inducedOrder (o : ModuleOrder D r) (t : Fin s → Term D r) : ModuleOrder D s where
  scalarOrder := o.scalarOrder
  termOrder := LinearOrder.lift' (key o t) (key_injective o t)
  wellFounded := InvImage.wf (key o t) wellFounded_lt
  shift_lt a u v h := by
    change key o t u < key o t v at h
    change key o t (shift a u) < key o t (shift a v)
    rw [key,key,Prod.Lex.toLex_lt_toLex] at h
    rw [key,key,Prod.Lex.toLex_lt_toLex]
    rcases h with h | ⟨he,hi⟩
    · left
      change o.LT (weight t (shift a u)) (weight t (shift a v))
      rw [weight_shift,weight_shift]
      exact o.shift_lt a (weight t u) (weight t v) h
    · right
      refine ⟨?_,hi⟩
      apply congrArg OrderedTerm.mk
      rw [weight_shift,weight_shift]
      exact congrArg (shift a) (congrArg OrderedTerm.val he)
  scalar_lt a b i hab := by
    change key o t (a,i) < key o t (b,i)
    apply Prod.Lex.toLex_lt_toLex.mpr
    left
    change o.LT (shift a (t i)) (shift b (t i))
    apply o.scalar_lt
    simpa only [map_add,add_comm] using add_lt_add_right hab (o.scalarOrder.toSyn (t i).1)

theorem induced_lt_iff (o : ModuleOrder D r) (t : Fin s → Term D r) (u v : Term D s) :
    (inducedOrder o t).LT u v ↔
      o.LT (weight t u) (weight t v) ∨ (weight t u=weight t v ∧ v.2<u.2) := by
  change key o t u < key o t v ↔ _
  simp only [key,Prod.Lex.toLex_lt_toLex,OrderedTerm.mk.injEq]
  rfl

theorem induced_le_iff (o : ModuleOrder D r) (t : Fin s → Term D r) (u v : Term D s) :
    (inducedOrder o t).LE u v ↔
      o.LT (weight t u) (weight t v) ∨ (weight t u=weight t v ∧ v.2≤u.2) := by
  change key o t u ≤ key o t v ↔ _
  simp only [key,Prod.Lex.toLex_le_toLex,OrderedTerm.mk.injEq]
  rfl

theorem weight_le_of_induced_le (o : ModuleOrder D r) (t : Fin s → Term D r)
    {u v : Term D s} (h : (inducedOrder o t).LE u v) : o.LE (weight t u) (weight t v) := by
  rcases (induced_le_iff o t u v).mp h with h | h
  · exact @le_of_lt _ o.termOrder.toPreorder _ _ h
  · exact @le_of_eq _ o.termOrder.toPreorder _ _ h.1

theorem induced_lt_of_weight_lt (o : ModuleOrder D r) (t : Fin s → Term D r)
    {u v : Term D s} (h : o.LT (weight t u) (weight t v)) : (inducedOrder o t).LT u v :=
  (induced_lt_iff o t u v).mpr (Or.inl h)

/-- The leading side of the i,j Schreyer syzygy (i<j) is its i component. -/
theorem primary_pair_lt (o : ModuleOrder D r) (t : Fin s → Term D r)
    (i j : Fin s) (hij : i<j) (hpos : (t i).2=(t j).2) :
    (inducedOrder o t).LT (((t i).1 ⊔ (t j).1)-(t j).1,j)
      (((t i).1 ⊔ (t j).1)-(t i).1,i) := by
  apply (induced_lt_iff o t _ _).mpr
  right
  refine ⟨?_,hij⟩
  apply Prod.ext
  · exact (tsub_add_cancel_of_le le_sup_right).trans (tsub_add_cancel_of_le le_sup_left).symm
  · exact hpos.symm

end
end Decoupling.HighDim.SchreyerSyzygy
