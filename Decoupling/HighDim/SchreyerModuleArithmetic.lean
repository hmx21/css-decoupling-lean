import Decoupling.HighDim.SchreyerModuleOrder

/-! # Leading-term arithmetic and actual cancellation in polynomial modules -/
namespace Decoupling.HighDim.SchreyerModule
noncomputable section
variable {K : Type*} [CommRing K] {D r : ℕ}

theorem bounded_add {o : ModuleOrder D r} {f g : Vec K D r} {t : Term D r}
    (hf : Bounded o f t) (hg : Bounded o g t) : Bounded o (f+g) t := by
  intro u hu
  by_cases hfu : coeff f u=0
  · apply hg
    intro hgu
    exact hu (by simp [hfu,hgu])
  · exact hf u hfu

theorem below_add {o : ModuleOrder D r} {f g : Vec K D r} {t : Term D r}
    (hf : StrictlyBelow o f t) (hg : StrictlyBelow o g t) : StrictlyBelow o (f+g) t := by
  intro u hu
  by_cases hfu : coeff f u=0
  · apply hg
    intro hgu
    exact hu (by simp [hfu,hgu])
  · exact hf u hfu

theorem bounded_neg {o : ModuleOrder D r} {f : Vec K D r} {t : Term D r}
    (hf : Bounded o f t) : Bounded o (-f) t := by
  intro u hu
  apply hf
  simpa only [coeff_neg,neg_ne_zero] using hu

theorem below_neg {o : ModuleOrder D r} {f : Vec K D r} {t : Term D r}
    (hf : StrictlyBelow o f t) : StrictlyBelow o (-f) t := by
  intro u hu
  apply hf
  simpa only [coeff_neg,neg_ne_zero] using hu

theorem bounded_sub {o : ModuleOrder D r} {f g : Vec K D r} {t : Term D r}
    (hf : Bounded o f t) (hg : Bounded o g t) : Bounded o (f-g) t := by
  rw [sub_eq_add_neg]
  exact bounded_add hf (bounded_neg hg)

theorem below_sub {o : ModuleOrder D r} {f g : Vec K D r} {t : Term D r}
    (hf : StrictlyBelow o f t) (hg : StrictlyBelow o g t) : StrictlyBelow o (f-g) t := by
  rw [sub_eq_add_neg]
  exact below_add hf (below_neg hg)

theorem below_sub_of_coeff_eq {o : ModuleOrder D r} {f g : Vec K D r} {t : Term D r}
    (hf : Bounded o f t) (hg : Bounded o g t) (hc : coeff f t=coeff g t) : StrictlyBelow o (f-g) t := by
  intro u hu
  apply o.lt_of_le_of_ne (bounded_sub hf hg u hu)
  intro he
  subst u
  exact hu (by simp [hc])

theorem bounded_monomial (o : ModuleOrder D r) (t : Term D r) (c : K) :
    Bounded o (monomial t c) t := by
  intro u hu
  by_cases he : t=u
  · subst u
    exact o.le_refl t
  · exact False.elim (hu (by simp [he]))

theorem isLeading_monomial (o : ModuleOrder D r) (t : Term D r) (c : K) (hc : c≠0) :
    IsLeading o (monomial t c) t :=
  ⟨by rw [coeff_monomial,ite_eq_left rfl]; exact hc,bounded_monomial o t c⟩

theorem coeff_monomial_smul_shift (a : Exponent D) (c : K) (f : Vec K D r) (t : Term D r) :
    coeff ((MvPolynomial.monomial a c : Poly K D) • f) (shift a t) = c*coeff f t := by
  exact MvPolynomial.coeff_monomial_mul _ _ _ _

theorem coeff_monomial_smul (a : Exponent D) (c : K) (f : Vec K D r) (t : Term D r) :
    coeff ((MvPolynomial.monomial a c : Poly K D) • f) t =
      if a≤t.1 then c*coeff f (t.1-a,t.2) else 0 := by
  exact MvPolynomial.coeff_monomial_mul' _ _ _ _

theorem coeff_monomial_smul_ne {a : Exponent D} {c : K} {f : Vec K D r} {t : Term D r}
    (ht : coeff ((MvPolynomial.monomial a c : Poly K D) • f) t ≠0) :
    ∃ u, shift a u=t ∧ coeff f u≠0 := by
  rw [coeff_monomial_smul] at ht
  split_ifs at ht with ha
  · exact ⟨(t.1-a,t.2),Prod.ext (add_tsub_cancel_of_le ha) rfl,right_ne_zero_of_mul ht⟩
  · exact False.elim (ht rfl)

theorem bounded_monomial_smul {o : ModuleOrder D r} {f : Vec K D r} {t : Term D r}
    (hf : Bounded o f t) (a : Exponent D) (c : K) :
    Bounded o ((MvPolynomial.monomial a c : Poly K D) • f) (shift a t) := by
  intro u hu
  obtain ⟨v,rfl,hv⟩ := coeff_monomial_smul_ne hu
  exact o.shift_le a (hf v hv)

theorem below_monomial_smul {o : ModuleOrder D r} {f : Vec K D r} {t : Term D r}
    (hf : StrictlyBelow o f t) (a : Exponent D) (c : K) :
    StrictlyBelow o ((MvPolynomial.monomial a c : Poly K D) • f) (shift a t) := by
  intro u hu
  obtain ⟨v,rfl,hv⟩ := coeff_monomial_smul_ne hu
  exact o.shift_lt a v t (hf v hv)

theorem bounded_sum {I : Type*} (s : Finset I) {o : ModuleOrder D r}
    (f : I → Vec K D r) (t : Term D r) (hf : ∀ i∈s,Bounded o (f i) t) :
    Bounded o (∑ i∈s,f i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact bounded_add (hf a (Finset.mem_insert_self _ _)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

theorem below_sum {I : Type*} (s : Finset I) {o : ModuleOrder D r}
    (f : I → Vec K D r) (t : Term D r) (hf : ∀ i∈s,StrictlyBelow o (f i) t) :
    StrictlyBelow o (∑ i∈s,f i) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact below_add (hf a (Finset.mem_insert_self _ _)) (ih (fun i hi => hf i (Finset.mem_insert_of_mem hi)))

variable [IsDomain K]

theorem IsLeading.monomial_smul {o : ModuleOrder D r} {f : Vec K D r} {t : Term D r}
    (hf : IsLeading o f t) (a : Exponent D) (c : K) (hc : c≠0) :
    IsLeading o ((MvPolynomial.monomial a c : Poly K D) • f) (shift a t) :=
  ⟨by rw [coeff_monomial_smul_shift]; exact mul_ne_zero hc hf.1,
    bounded_monomial_smul hf.2 a c⟩

end
end Decoupling.HighDim.SchreyerModule
