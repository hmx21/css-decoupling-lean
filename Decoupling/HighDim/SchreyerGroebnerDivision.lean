import Decoupling.HighDim.SchreyerGroebner
import Decoupling.HighDim.SchreyerDivision

/-!
# Gröbner divisibility implies generation and bounded standard representations

Membership in the actual input submodule forces the proved division
remainder to vanish. Consequently the finite Gröbner family generates
that submodule; generation was not assumed in its definition.
-/
namespace Decoupling.HighDim.SchreyerModule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D r s : ℕ}
variable {o : ModuleOrder D r} {G : Fin s → Vec K D r}
  {N : Submodule (Poly K D) (Vec K D r)}

theorem IsGroebnerBasis.remainder_zero (hG : IsGroebnerBasis o G N)
    {f rem : Vec K D r} (q : Fin s → Poly K D) (hf : f∈N)
    (he : f=(∑ i,q i • G i)+rem) (hr : Reduced o G rem) : rem=0 := by
  classical
  have hs : (∑ i,q i • G i)∈N := Submodule.sum_mem N (fun i _ => N.smul_mem _ (hG.mem i))
  have hm : rem∈N := by
    have hsub := N.sub_mem hf hs
    rwa [he,add_sub_cancel_left] at hsub
  by_contra hz
  obtain ⟨i,u,hi,hd⟩ := hG.leading rem hm (lm o rem hz) (lm_isLeading o rem hz)
  exact hr _ (lc_ne_zero o rem hz) i u hi hd

/-- The representation and its bound use actual polynomial-module products. -/
theorem IsGroebnerBasis.standardRepresentation (hG : IsGroebnerBasis o G N)
    {f : Vec K D r} (hf : f∈N) :
    ∃ q : Fin s → Poly K D,
      f=∑ i,q i • G i ∧ ∀ t,Bounded o f t → ∀ i,Bounded o (q i • G i) t := by
  obtain ⟨q,rem,he,hr,hb⟩ := division o G f
  have hz := hG.remainder_zero q hf he hr
  refine ⟨q,?_,fun t ht => (hb t ht).1⟩
  simpa only [hz,add_zero] using he

theorem IsGroebnerBasis.standardRepresentation_bounded (hG : IsGroebnerBasis o G N)
    {f : Vec K D r} {t : Term D r} (hf : f∈N) (ht : Bounded o f t) :
    ∃ q : Fin s → Poly K D, f=∑ i,q i • G i ∧ ∀ i,Bounded o (q i • G i) t := by
  obtain ⟨q,he,hq⟩ := hG.standardRepresentation hf
  exact ⟨q,he,hq t ht⟩

/-- Used for S-pairs: all correction summands stay strictly below the lcm term. -/
theorem IsGroebnerBasis.standardRepresentation_strict (hG : IsGroebnerBasis o G N)
    {f : Vec K D r} {t : Term D r} (hf : f∈N) (ht : StrictlyBelow o f t) :
    ∃ q : Fin s → Poly K D, f=∑ i,q i • G i ∧ ∀ i,StrictlyBelow o (q i • G i) t := by
  by_cases hz : f=0
  · refine ⟨0,?_,?_⟩
    · simp [hz]
    · intro i
      simpa only [Pi.zero_apply,zero_smul] using below_zero (K := K) o t
  · obtain ⟨q,he,hq⟩ := hG.standardRepresentation_bounded hf (lm_isLeading o f hz).2
    exact ⟨q,he,fun i => below_of_bounded_of_lt (hq i) (ht _ (lc_ne_zero o f hz))⟩

/-- Actual generation is a theorem, not a hidden Gröbner structure field. -/
theorem IsGroebnerBasis.span_eq (hG : IsGroebnerBasis o G N) :
    Submodule.span (Poly K D) (Set.range G)=N := by
  apply le_antisymm
  · exact Submodule.span_le.mpr (by rintro _ ⟨i,rfl⟩; exact hG.mem i)
  · intro f hf
    obtain ⟨q,he,_⟩ := hG.standardRepresentation hf
    rw [he]
    exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i,rfl⟩))

/-- The unconditional finite minimal GB theorem together with its proved span. -/
theorem exists_minimal_groebner_generating (o : ModuleOrder D r)
    (N : Submodule (Poly K D) (Vec K D r)) :
    ∃ s : ℕ, ∃ G : Fin s → Vec K D r,
      IsGroebnerBasis o G N ∧ IsMinimal o G ∧ Submodule.span (Poly K D) (Set.range G)=N := by
  obtain ⟨s,G,hG,hmin⟩ := exists_minimal_groebner o N
  exact ⟨s,G,hG,hmin,hG.span_eq⟩

end
end Decoupling.HighDim.SchreyerModule
