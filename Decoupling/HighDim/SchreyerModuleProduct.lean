import Decoupling.HighDim.SchreyerModuleArithmetic

/-!
# Actual leading terms of polynomial multiples of module vectors

The scalar and module orders are those in ModuleOrder. Every comparison
uses its explicit termOrder; no default product order is substituted.
The results follow from actual polynomial coefficients and order axioms.
-/
namespace Decoupling.HighDim.SchreyerModule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D r : ℕ}

theorem ModuleOrder.scalar_le (o : ModuleOrder D r) {a b : Exponent D} (i : Fin r)
    (h : o.scalarOrder.toSyn a ≤ o.scalarOrder.toSyn b) : o.LE (a,i) (b,i) := by
  rcases eq_or_lt_of_le h with he|hl
  · have hab := o.scalarOrder.toSyn.injective he
    subst b
    exact o.le_refl _
  · exact @le_of_lt _ o.termOrder.toPreorder _ _ (o.scalar_lt a b i hl)

theorem ModuleOrder.scalar_le_of_term_le (o : ModuleOrder D r) {a b : Exponent D} {i : Fin r}
    (h : o.LE (a,i) (b,i)) : o.scalarOrder.toSyn a ≤ o.scalarOrder.toSyn b := by
  by_contra hn
  have hl := o.scalar_lt b a i (lt_of_not_ge hn)
  exact (@not_lt_of_ge _ o.termOrder.toPreorder _ _ h) hl

theorem ModuleOrder.scalar_shift_le (o : ModuleOrder D r) (t : Term D r) {a b : Exponent D}
    (h : o.scalarOrder.toSyn a ≤ o.scalarOrder.toSyn b) : o.LE (shift a t) (shift b t) := by
  apply o.scalar_le
  simpa only [shift,map_add,add_comm] using add_le_add_right h (o.scalarOrder.toSyn t.1)

variable {K : Type*} [CommRing K]

theorem IsLeading.component_degree {o : ModuleOrder D r} {f : Vec K D r} {t : Term D r}
    (hf : IsLeading o f t) : o.scalarOrder.degree (f t.2) = t.1 := by
  have hfn : f t.2 ≠ 0 := by
    intro hz
    exact hf.1 (by simp [coeff,hz])
  have hd : coeff f (o.scalarOrder.degree (f t.2),t.2) ≠ 0 :=
    o.scalarOrder.coeff_degree_ne_zero_iff.mpr hfn
  apply o.scalarOrder.toSyn.injective
  exact le_antisymm (o.scalar_le_of_term_le (hf.2 _ hd))
    (o.scalarOrder.le_degree (MvPolynomial.mem_support_iff.mpr hf.1))

theorem bounded_polynomial_smul {o : ModuleOrder D r} {f : Vec K D r} {t : Term D r}
    (hf : Bounded o f t) (q : Poly K D) :
    Bounded o (q • f) (shift (o.scalarOrder.degree q) t) := by
  classical
  have he : q • f = ∑ a ∈ q.support, (MvPolynomial.monomial a (q.coeff a) : Poly K D) • f := by
    conv_lhs => rw [q.as_sum]
    rw [Finset.sum_smul]
  rw [he]
  apply bounded_sum
  intro a ha
  exact bounded_mono (bounded_monomial_smul hf a (q.coeff a))
    (o.scalar_shift_le t (o.scalarOrder.le_degree ha))

theorem coeff_polynomial_smul_leading {o : ModuleOrder D r} {f : Vec K D r} {t : Term D r}
    (hf : IsLeading o f t) (q : Poly K D) :
    coeff (q • f) (shift (o.scalarOrder.degree q) t) =
      o.scalarOrder.leadingCoeff q * coeff f t := by
  change (q * f t.2).coeff (o.scalarOrder.degree q+t.1) =
    o.scalarOrder.leadingCoeff q * (f t.2).coeff t.1
  rw [← hf.component_degree]
  exact o.scalarOrder.coeff_mul_of_degree_add

variable [IsDomain K]

theorem IsLeading.polynomial_smul {o : ModuleOrder D r} {f : Vec K D r} {t : Term D r}
    (hf : IsLeading o f t) (q : Poly K D) (hq : q ≠ 0) :
    IsLeading o (q • f) (shift (o.scalarOrder.degree q) t) := by
  refine ⟨?_,bounded_polynomial_smul hf.2 q⟩
  rw [coeff_polynomial_smul_leading hf q]
  exact mul_ne_zero (o.scalarOrder.leadingCoeff_ne_zero_iff.mpr hq) hf.1

theorem lm_polynomial_smul {o : ModuleOrder D r} {f : Vec K D r} {t : Term D r}
    (hf : IsLeading o f t) (q : Poly K D) (hq : q ≠ 0) :
    lm o (q • f) (hf.polynomial_smul q hq).ne_zero = shift (o.scalarOrder.degree q) t :=
  isLeading_lm o (hf.polynomial_smul q hq)

theorem lc_polynomial_smul {o : ModuleOrder D r} {f : Vec K D r} {t : Term D r}
    (hf : IsLeading o f t) (q : Poly K D) (hq : q ≠ 0) :
    lc o (q • f) (hf.polynomial_smul q hq).ne_zero =
      o.scalarOrder.leadingCoeff q * coeff f t := by
  rw [lc,lm_polynomial_smul hf q hq,coeff_polynomial_smul_leading hf q]

/-- Every supported scalar monomial remains below a bound on the actual product. -/
theorem polynomial_smul_below_coeff {o : ModuleOrder D r} {f : Vec K D r} {t T : Term D r}
    (hf : IsLeading o f t) {q : Poly K D} (hb : StrictlyBelow o (q • f) T)
    (a : Exponent D) (ha : q.coeff a ≠ 0) : o.LT (shift a t) T := by
  have hq : q ≠ 0 := by intro he; exact ha (by simp [he])
  have hp := hf.polynomial_smul q hq
  exact @lt_of_le_of_lt _ o.termOrder.toPreorder _ _ _
    (o.scalar_shift_le t (o.scalarOrder.le_degree (MvPolynomial.mem_support_iff.mpr ha)))
    (hb _ hp.1)

end
end Decoupling.HighDim.SchreyerModule
