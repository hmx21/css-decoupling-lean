import Decoupling.HighDim.SchreyerGroebnerCompletion

/-!
# Finite-stage invariants of mathematical Buchberger completion

A step records a concrete normalized S-pair and genuine normal-form
remainder data. Every step preserves the actual module and strictly
increases its initial module. The resulting relation is well founded
in the execution direction and reaches a finite terminal family.
This is a mathematical nondeterministic completion relation; it makes no
claim about a runtime coefficient-array implementation or its operation count.
-/
namespace Decoupling.HighDim.SchreyerModule
open SchreyerSyzygy
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] {D r : ℕ}

abbrev Family (K : Type*) [Field K] (D r : ℕ) := (s : ℕ) × (Fin s → Vec K D r)

def familySpan (G : Family K D r) := Submodule.span (Poly K D) (Set.range G.2)
def familyInitial (o : ModuleOrder D r) (G : Family K D r) := initialSpan o G.2

def CompletionStep (o : ModuleOrder D r) (G H : Family K D r) : Prop :=
  ∃ i j u v, IsLeading o (G.2 i) u ∧ IsLeading o (G.2 j) v ∧ u.2=v.2 ∧
    ∃ q : Fin G.1 → Poly K D, ∃ rem : Vec K D r,
      sPolynomial (G.2 i) (G.2 j) u v=(∑ k,q k • G.2 k)+rem ∧
      Reduced o G.2 rem ∧ (∀ k,StrictlyBelow o (q k • G.2 k) (pairTop u v)) ∧
      StrictlyBelow o rem (pairTop u v) ∧ rem≠0 ∧ H=⟨G.1+1,Fin.snoc G.2 rem⟩

theorem CompletionStep.initial_lt {o : ModuleOrder D r} {G H : Family K D r}
    (h : CompletionStep o G H) : familyInitial o G < familyInitial o H := by
  obtain ⟨i,j,u,v,hi,hj,hp,q,rem,he,hred,hq,hr,hn,rfl⟩ := h
  exact initialSpan_lt_snoc o G.2 rem hn hred

theorem CompletionStep.span_eq {o : ModuleOrder D r} {G H : Family K D r}
    (h : CompletionStep o G H) : familySpan H=familySpan G := by
  obtain ⟨i,j,u,v,hi,hj,hp,q,rem,he,hred,hq,hr,hn,rfl⟩ := h
  apply span_snoc_eq G.2 rem
  have hpair := sPolynomial_mem (N := familySpan G)
    (Submodule.subset_span ⟨i,rfl⟩) (Submodule.subset_span ⟨j,rfl⟩) u v
  have hsum : (∑ k,q k • G.2 k)∈familySpan G :=
    Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,rfl⟩))
  have hsub := (familySpan G).sub_mem hpair hsum
  rwa [he,add_sub_cancel_left] at hsub

theorem CompletionStep.retains {o : ModuleOrder D r} {G H : Family K D r}
    (h : CompletionStep o G H) : Set.range G.2 ⊆ Set.range H.2 := by
  obtain ⟨i,j,u,v,hi,hj,hp,q,rem,he,hred,hq,hr,hn,rfl⟩ := h
  rintro _ ⟨k,rfl⟩
  exact ⟨k.castSucc,by simp⟩

/-- Every proper completion step decreases a proved well-founded relation. -/
theorem completion_wellFounded (o : ModuleOrder D r) :
    WellFounded (fun H G : Family K D r => CompletionStep o G H) := by
  let : IsNoetherianRing (Poly K D) := inferInstance
  let : IsNoetherian (Poly K D) (Vec K D r) := inferInstance
  exact Subrelation.wf (fun h => CompletionStep.initial_lt h)
    (InvImage.wf (familyInitial o) wellFounded_gt)

/-- At a terminal state every S-pair has the required strict standard expression. -/
theorem closedPairs_of_terminal (o : ModuleOrder D r) (G : Family K D r)
    (h : ¬∃ H,CompletionStep o G H) : ClosedPairs o G.2 := by
  intro i j u v hi hj hp
  obtain ⟨q,rem,he,hred,hq,hr⟩ := division_strict o G.2 _ _ (sPolynomial_below hi hj hp)
  have hz : rem=0 := by
    by_contra hn
    exact h ⟨⟨G.1+1,Fin.snoc G.2 rem⟩,i,j,u,v,hi,hj,hp,q,rem,he,hred,hq,hr,hn,rfl⟩
  exact ⟨q,by simpa only [hz,add_zero] using he,hq⟩

/-- A finite sequence of the actual completion steps, with span retained. -/
theorem exists_terminal_completion_path (o : ModuleOrder D r) (G : Family K D r) :
    ∃ H : Family K D r,
      Relation.ReflTransGen (CompletionStep o) G H ∧
      (¬∃ J,CompletionStep o H J) ∧ familySpan H=familySpan G := by
  classical
  refine (completion_wellFounded o).induction (C := fun G : Family K D r =>
    ∃ H : Family K D r,Relation.ReflTransGen (CompletionStep o) G H ∧
      (¬∃ J,CompletionStep o H J) ∧ familySpan H=familySpan G) G ?_
  intro G ih
  by_cases h : ∃ H,CompletionStep o G H
  · obtain ⟨H,hGH⟩ := h
    obtain ⟨J,hpath,hterm,hspan⟩ := ih H hGH
    exact ⟨J,Relation.ReflTransGen.head hGH hpath,hterm,hspan.trans hGH.span_eq⟩
  · exact ⟨G,Relation.ReflTransGen.refl,h,rfl⟩

theorem exists_closed_completion_path (o : ModuleOrder D r) (G : Family K D r) :
    ∃ H : Family K D r,
      Relation.ReflTransGen (CompletionStep o) G H ∧
      familySpan H=familySpan G ∧ ClosedPairs o H.2 := by
  obtain ⟨H,hpath,hterm,hspan⟩ := exists_terminal_completion_path o G
  exact ⟨H,hpath,hspan,closedPairs_of_terminal o H hterm⟩

end
end Decoupling.HighDim.SchreyerModule
