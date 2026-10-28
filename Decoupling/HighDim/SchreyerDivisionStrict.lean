import Decoupling.HighDim.SchreyerDivision

/-! # Strict standard-term bounds for normal-form division -/
namespace Decoupling.HighDim.SchreyerModule
noncomputable section
variable {K : Type*} [Field K] {D r s : ℕ}

theorem division_strict (o : ModuleOrder D r) (G : Fin s → Vec K D r)
    (f : Vec K D r) (t : Term D r) (ht : StrictlyBelow o f t) :
    ∃ q : Fin s → Poly K D, ∃ rem : Vec K D r,
      f=(∑ i,q i • G i)+rem ∧ Reduced o G rem ∧
      (∀ i,StrictlyBelow o (q i • G i) t) ∧ StrictlyBelow o rem t := by
  by_cases hf : f=0
  · subst f
    refine ⟨0,0,by simp,reduced_zero o G,?_,below_zero o t⟩
    intro i
    simpa only [Pi.zero_apply,zero_smul] using below_zero (K := K) o t
  · obtain ⟨q,rem,hr⟩ := division_at_leading o G (lm o f hf) f (lm_isLeading o f hf)
    have hlt := ht _ (lc_ne_zero o f hf)
    exact ⟨q,rem,hr.equation,hr.reduced,
      fun i => below_of_bounded_of_lt (hr.bound i) hlt,
      below_of_bounded_of_lt hr.remainder_bound hlt⟩

end
end Decoupling.HighDim.SchreyerModule
