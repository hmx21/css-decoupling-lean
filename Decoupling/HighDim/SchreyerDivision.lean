import Decoupling.HighDim.SchreyerModuleArithmetic

/-!
# Mathematical module normal-form division, with standard representations

A well-founded leading-term reduction produces actual polynomial
coefficients and an irreducible remainder for every finite input family.
Zero family members are allowed and never divided by. No Gröbner property
is assumed. This is a proved existence/construction theorem, not yet an
executable finite-array division implementation.
-/
namespace Decoupling.HighDim.SchreyerModule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] {D r s : ℕ}

/-- No supported remainder term is divisible by a leading term of the family. -/
def Reduced (o : ModuleOrder D r) (G : Fin s → Vec K D r) (rem : Vec K D r) : Prop :=
  ∀ t, coeff rem t≠0 → ∀ i u, IsLeading o (G i) u → ¬Divides u t

structure DivisionAt (o : ModuleOrder D r) (G : Fin s → Vec K D r)
    (f : Vec K D r) (t : Term D r) (q : Fin s → Poly K D) (rem : Vec K D r) : Prop where
  equation : f=(∑ i,q i • G i)+rem
  bound : ∀ i,Bounded o (q i • G i) t
  remainder_bound : Bounded o rem t
  reduced : Reduced o G rem

@[simp] theorem reduced_zero (o : ModuleOrder D r) (G : Fin s → Vec K D r) :
    Reduced o G 0 := by intro t ht; exact False.elim (ht (coeff_zero t))

theorem DivisionAt.mono {o : ModuleOrder D r} {G : Fin s → Vec K D r}
    {f : Vec K D r} {t u : Term D r} {q : Fin s → Poly K D} {rem : Vec K D r}
    (h : DivisionAt o G f t q rem) (htu : o.LE t u) : DivisionAt o G f u q rem :=
  ⟨h.equation,fun i => bounded_mono (h.bound i) htu,bounded_mono h.remainder_bound htu,h.reduced⟩

theorem division_zero (o : ModuleOrder D r) (G : Fin s → Vec K D r) (t : Term D r) :
    DivisionAt o G 0 t 0 0 := by
  refine ⟨by simp,?_,bounded_zero o t,reduced_zero o G⟩
  intro i
  simpa only [Pi.zero_apply,zero_smul] using bounded_zero (K := K) o t

/-- One genuine leading-term cancellation strictly lowers all remaining terms. -/
theorem cancel_leading {o : ModuleOrder D r} {f g : Vec K D r} {t u : Term D r}
    (hf : IsLeading o f t) (hg : IsLeading o g u) (hdiv : Divides u t) :
    ∃ a : Exponent D, ∃ c : K,
      Bounded o ((MvPolynomial.monomial a c : Poly K D) • g) t ∧
      StrictlyBelow o (f-(MvPolynomial.monomial a c : Poly K D) • g) t := by
  obtain ⟨a,ha⟩ := (divides_iff_shift u t).mp hdiv
  let c := coeff f t / coeff g u
  have hb : Bounded o ((MvPolynomial.monomial a c : Poly K D) • g) t := by
    rw [←ha]
    exact bounded_monomial_smul hg.2 a c
  refine ⟨a,c,hb,below_sub_of_coeff_eq hf.2 hb ?_⟩
  rw [←ha,coeff_monomial_smul_shift]
  change coeff f (shift a u)=(coeff f t / coeff g u)*coeff g u
  rw [ha,div_mul_cancel₀ _ hg.1]

/-- Division with a bound supplied by the input's actual leading term. -/
theorem division_at_leading (o : ModuleOrder D r) (G : Fin s → Vec K D r) :
    ∀ t, ∀ f : Vec K D r, IsLeading o f t →
      ∃ q rem,DivisionAt o G f t q rem := by
  classical
  intro t
  refine o.wellFounded.induction (C := fun t => ∀ f : Vec K D r, IsLeading o f t → ∃ q rem,DivisionAt o G f t q rem) t ?_
  intro t ih f hf
  have recur (g : Vec K D r) (hg : StrictlyBelow o g t) :
      ∃ q rem,DivisionAt o G g t q rem := by
    by_cases hz : g=0
    · subst g
      exact ⟨0,0,division_zero o G t⟩
    · obtain ⟨q,rem,hr⟩ := ih (lm o g hz) ((below_iff_lm_lt o g hz t).mp hg) g (lm_isLeading o g hz)
      exact ⟨q,rem,hr.mono (@le_of_lt _ o.termOrder.toPreorder _ _ ((below_iff_lm_lt o g hz t).mp hg))⟩
  by_cases hd : ∃ i u, IsLeading o (G i) u ∧ Divides u t
  · obtain ⟨i,u,hGi,hdiv⟩ := hd
    obtain ⟨a,c,hb,hl⟩ := cancel_leading hf hGi hdiv
    obtain ⟨q,rem,hr⟩ := recur (f-(MvPolynomial.monomial a c : Poly K D) • G i) hl
    let p : Poly K D := MvPolynomial.monomial a c
    let q' : Fin s → Poly K D := q+Pi.single i p
    have hs : (∑ j,q' j • G j)=(∑ j,q j • G j)+p • G i := by
      simp [q',Pi.add_apply,add_smul,Finset.sum_add_distrib,Pi.single_apply,ite_smul]
    refine ⟨q',rem,?_,?_,hr.remainder_bound,hr.reduced⟩
    · rw [hs]
      have he := sub_eq_iff_eq_add.mp hr.equation
      change f=((∑ j,q j • G j)+rem)+p • G i at he
      rw [he]
      ac_rfl
    · intro j
      by_cases hj : j=i
      · subst j
        simpa [q',add_smul] using bounded_add (hr.bound i) hb
      · simpa [q',hj] using hr.bound j
  · let lead := monomial t (coeff f t)
    have hl : StrictlyBelow o (f-lead) t :=
      below_sub_of_coeff_eq hf.2 (bounded_monomial o t _) (by simp [lead])
    obtain ⟨q,rem,hr⟩ := recur (f-lead) hl
    refine ⟨q,rem+lead,?_,hr.bound,bounded_add hr.remainder_bound (bounded_monomial o t _),?_⟩
    · have he := sub_eq_iff_eq_add.mp hr.equation
      simpa only [add_assoc] using he
    · intro u hu i v hGi hdiv
      by_cases hrem : coeff rem u=0
      · have htu : t=u := by
          by_contra hne
          exact hu (by simp [lead,hrem,hne])
        subst u
        exact hd ⟨i,v,hGi,hdiv⟩
      · exact hr.reduced u hrem i v hGi hdiv

/-- Uniform bound formulation, including the zero vector and rank zero. -/
theorem division (o : ModuleOrder D r) (G : Fin s → Vec K D r) (f : Vec K D r) :
    ∃ q : Fin s → Poly K D, ∃ rem : Vec K D r,
      f=(∑ i,q i • G i)+rem ∧ Reduced o G rem ∧
      ∀ t,Bounded o f t → (∀ i,Bounded o (q i • G i) t) ∧ Bounded o rem t := by
  by_cases hf : f=0
  · subst f
    refine ⟨0,0,by simp,reduced_zero o G,?_⟩
    intro t _
    exact ⟨fun i => by simpa only [Pi.zero_apply,zero_smul] using bounded_zero (K := K) o t,bounded_zero o t⟩
  · obtain ⟨q,rem,hr⟩ := division_at_leading o G (lm o f hf) f (lm_isLeading o f hf)
    refine ⟨q,rem,hr.equation,hr.reduced,?_⟩
    intro t ht
    have h := hr.mono (ht _ (lc_ne_zero o f hf))
    exact ⟨h.bound,h.remainder_bound⟩

end
end Decoupling.HighDim.SchreyerModule
