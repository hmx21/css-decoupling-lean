import Decoupling.HighDim.SchreyerModuleProduct
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Distinct leading positions imply polynomial-linear independence

A nonzero finite relation would have a unique maximal product-leading term.
The exact coefficient of that term cannot cancel. No Gröbner-basis or
freeness certificate is a premise, and the index family may be empty.
-/
namespace Decoupling.HighDim.SchreyerModule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [CommRing K] [IsDomain K] {D r : ℕ} {ι : Type*}

theorem linearIndependent_of_leading_positions (o : ModuleOrder D r)
    (G : ι → Vec K D r) (t : ι → Term D r)
    (hG : ∀ i, IsLeading o (G i) (t i))
    (hpos : Function.Injective fun i => (t i).2) : LinearIndependent (Poly K D) G := by
  classical
  apply linearIndependent_iff'.mpr
  intro s q hsum i hi
  by_contra hqi
  let active := s.filter fun j => q j ≠ 0
  have ha : active.Nonempty := ⟨i,Finset.mem_filter.mpr ⟨hi,hqi⟩⟩
  let lead (j : ι) := shift (o.scalarOrder.degree (q j)) (t j)
  obtain ⟨j,hj,hmax⟩ := @Finset.exists_max_image (Term D r) ι o.termOrder active lead ha
  have hjs : j ∈ s := (Finset.mem_filter.mp hj).1
  have hqj : q j ≠ 0 := (Finset.mem_filter.mp hj).2
  have hcoeff (k : ι) (hk : k ∈ s) (hkj : k ≠ j) : coeff (q k • G k) (lead j) = 0 := by
    by_cases hqk : q k = 0
    · simp [hqk]
    have hkactive : k ∈ active := Finset.mem_filter.mpr ⟨hk,hqk⟩
    have hne : lead k ≠ lead j := by
      intro he
      apply hkj
      apply hpos
      change (lead k).2 = (lead j).2
      exact congrArg Prod.snd he
    have hlt : o.LT (lead k) (lead j) := o.lt_of_le_of_ne (hmax k hkactive) hne
    by_contra hn
    have hb := bounded_polynomial_smul (hG k).2 (q k) (lead j) hn
    exact (@lt_irrefl _ o.termOrder.toPreorder (lead j))
      (@lt_of_le_of_lt _ o.termOrder.toPreorder _ _ _ hb hlt)
  have he : coeff (∑ k ∈ s, q k • G k) (lead j) = coeff (q j • G j) (lead j) := by
    simp only [coeff,Finset.sum_apply,MvPolynomial.coeff_sum]
    change (∑ k ∈ s, coeff (q k • G k) (lead j)) = coeff (q j • G j) (lead j)
    exact Finset.sum_eq_single j hcoeff (fun h => False.elim (h hjs))
  apply ((hG j).polynomial_smul (q j) hqj).1
  change coeff (q j • G j) (lead j) = 0
  rw [← he,hsum,coeff_zero]

end
end Decoupling.HighDim.SchreyerModule
