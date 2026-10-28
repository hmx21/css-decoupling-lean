import Decoupling.HighDim.SchreyerGroebnerInitial
import Decoupling.HighDim.SchreyerDivisionStrict
import Decoupling.HighDim.SchreyerSyzygyPair

/-!
# Finite mathematical Buchberger completion

Successively inserting nonzero S-pair division remainders preserves the
actual span and strictly increases the initial module. Noetherian
well-founded induction therefore yields a finite family with every S-pair
standard-representable below its lcm term. This is a mathematical
construction and termination proof; no executable array implementation or
Buchberger correctness criterion is silently asserted here.
-/
namespace Decoupling.HighDim.SchreyerModule
open SchreyerSyzygy
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] {D r s : ℕ}

def ClosedPairs (o : ModuleOrder D r) (G : Fin s → Vec K D r) : Prop :=
  ∀ i j u v, IsLeading o (G i) u → IsLeading o (G j) v → u.2=v.2 →
    ∃ q : Fin s → Poly K D,
      sPolynomial (G i) (G j) u v = ∑ k,q k • G k ∧
      ∀ k,StrictlyBelow o (q k • G k) (pairTop u v)

theorem IsGroebnerBasis.closedPairs {o : ModuleOrder D r} {G : Fin s → Vec K D r}
    {N : Submodule (Poly K D) (Vec K D r)} (hG : IsGroebnerBasis o G N) : ClosedPairs o G := by
  intro i j u v hi hj hp
  exact hG.standardRepresentation_strict (sPolynomial_mem (hG.mem i) (hG.mem j) u v)
    (sPolynomial_below hi hj hp)

/-- Unconditional finite completion from any finite family. The original
span, and every original generator, are retained. -/
theorem exists_closed_completion (o : ModuleOrder D r) (G : Fin s → Vec K D r) :
    ∃ n : ℕ, ∃ H : Fin n → Vec K D r,
      Submodule.span (Poly K D) (Set.range H)=Submodule.span (Poly K D) (Set.range G) ∧
      Set.range G ⊆ Set.range H ∧ ClosedPairs o H := by
  classical
  let : IsNoetherianRing (Poly K D) := inferInstance
  let : IsNoetherian (Poly K D) (Vec K D r) := inferInstance
  have main : ∀ I : Submodule (Poly K D) (Vec K D r),
      ∀ s : ℕ, ∀ G : Fin s → Vec K D r,initialSpan o G=I →
        ∃ n : ℕ, ∃ H : Fin n → Vec K D r,
          Submodule.span (Poly K D) (Set.range H)=Submodule.span (Poly K D) (Set.range G) ∧
          Set.range G ⊆ Set.range H ∧ ClosedPairs o H := by
    intro I
    refine wellFounded_gt.induction (C := fun I : Submodule (Poly K D) (Vec K D r) =>
      ∀ s : ℕ, ∀ G : Fin s → Vec K D r,initialSpan o G=I →
        ∃ n : ℕ, ∃ H : Fin n → Vec K D r,
          Submodule.span (Poly K D) (Set.range H)=Submodule.span (Poly K D) (Set.range G) ∧
          Set.range G ⊆ Set.range H ∧ ClosedPairs o H) I ?_
    intro I ih s G hI
    subst I
    by_cases hc : ClosedPairs o G
    · exact ⟨s,G,rfl,Set.Subset.refl _,hc⟩
    · simp only [ClosedPairs,not_forall] at hc
      obtain ⟨i,j,u,v,hi,hj,hpos,hbad⟩ := hc
      obtain ⟨q,rem,he,hred,hq,hrbelow⟩ := division_strict o G
        (sPolynomial (G i) (G j) u v) (pairTop u v) (sPolynomial_below hi hj hpos)
      have hr : rem≠0 := by
        intro hz
        apply hbad
        exact ⟨q,by simpa only [hz,add_zero] using he,hq⟩
      have hrem : rem∈Submodule.span (Poly K D) (Set.range G) := by
        have hp := sPolynomial_mem (N := Submodule.span (Poly K D) (Set.range G)) (Submodule.subset_span ⟨i,rfl⟩) (Submodule.subset_span ⟨j,rfl⟩) u v
        have hs : (∑ k,q k • G k)∈Submodule.span (Poly K D) (Set.range G) :=
          Submodule.sum_mem _ (fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k,rfl⟩))
        have hd := (Submodule.span (Poly K D) (Set.range G)).sub_mem hp hs
        rwa [he,add_sub_cancel_left] at hd
      obtain ⟨n,H,hspan,hretain,hclosed⟩ := ih (initialSpan o (Fin.snoc G rem))
        (initialSpan_lt_snoc o G rem hr hred) (s+1) (Fin.snoc G rem) rfl
      refine ⟨n,H,hspan.trans (span_snoc_eq G rem hrem),?_,hclosed⟩
      rintro _ ⟨k,rfl⟩
      apply hretain
      exact ⟨k.castSucc,Fin.snoc_castSucc _ _ k⟩
  exact main (initialSpan o G) s G rfl

end
end Decoupling.HighDim.SchreyerModule
