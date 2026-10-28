import Decoupling.HighDim.SchreyerSyzygyMap

/-!
# A cancelled weighted leading coefficient forces a Schreyer pair

This is the common algebraic core for the syzygy theorem and Buchberger's
criterion. It assumes neither a Gröbner basis nor a kernel certificate:
only the actual chosen weighted coefficient of the image is zero.
-/
namespace Decoupling.HighDim.SchreyerSyzygy
open SchreyerModule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D r s : ℕ}

private theorem other_nonzero (c : Fin s → K) (i : Fin s)
    (hs : ∑ j,c j=0) (hi : c i≠0) : ∃ j,j≠i ∧ c j≠0 := by
  classical
  by_contra hn
  have hj (j : Fin s) (hji : j≠i) : c j=0 := by
    by_contra hc
    exact hn ⟨j,hji,hc⟩
  have he : (∑ j,c j)=c i := Finset.sum_eq_single i (fun j _ hji => hj j hji) (by simp)
  exact hi (he.symm.trans hs)

/-- A later source coordinate has a nonzero coefficient at exactly the
same weighted leading term whenever that image coefficient cancels. -/
theorem leading_partner_of_image_coeff_zero {o : ModuleOrder D r}
    (G : Fin s → Vec K D r) (t : Fin s → Term D r) (hG : ∀ i,IsLeading o (G i) (t i))
    {z : Vec K D s} {u : Term D s} (hz : IsLeading (inducedOrder o t) z u)
    (hzero : coeff (columnMap G z) (weight t u)=0) :
    ∃ j a,u.2<j ∧ weight t (a,j)=weight t u ∧ coeff z (a,j)≠0 := by
  have hi := (principal_product_leading G t hG hz).1
  rw [columnMap_coeff] at hzero
  obtain ⟨j,hji,hj⟩ := other_nonzero (fun j => coeff (z j • G j) (weight t u)) u.2 hzero hi
  have hq : z j≠0 := by
    intro he
    exact hj (by simp [he])
  let a := o.scalarOrder.degree (z j)
  have ha : coeff z (a,j)≠0 := o.scalarOrder.coeff_degree_ne_zero_iff.mpr hq
  have hzj := hz.2 (a,j) ha
  have hforward := weight_le_of_induced_le o t hzj
  have hbackward := ((hG j).polynomial_smul (z j) hq).2 (weight t u) hj
  have he : weight t (a,j)=weight t u :=
    @le_antisymm _ o.termOrder.toPartialOrder _ _ hforward hbackward
  have hij : u.2≤j := by
    rcases (induced_le_iff o t (a,j) u).mp hzj with hlt | hle
    · have hc : o.LT (weight t u) (weight t u) := he ▸ hlt
      exact False.elim ((@lt_irrefl _ o.termOrder.toPreorder _) hc)
    · exact hle.2
  exact ⟨j,a,lt_of_le_of_ne hij (Ne.symm hji),he,ha⟩

/-- The leading lcm quotient of that pair divides the actual source leader. -/
theorem pair_divides_of_image_coeff_zero {o : ModuleOrder D r}
    (G : Fin s → Vec K D r) (t : Fin s → Term D r) (hG : ∀ i,IsLeading o (G i) (t i))
    {z : Vec K D s} {u : Term D s} (hz : IsLeading (inducedOrder o t) z u)
    (hzero : coeff (columnMap G z) (weight t u)=0) :
    ∃ j,u.2<j ∧ (t u.2).2=(t j).2 ∧
      Divides (((t u.2).1 ⊔ (t j).1)-(t u.2).1,u.2) u := by
  obtain ⟨j,a,hij,he,_⟩ := leading_partner_of_image_coeff_zero G t hG hz hzero
  have hpos : (t u.2).2=(t j).2 := (congrArg Prod.snd he).symm
  have hsum : a+(t j).1=u.1+(t u.2).1 := congrArg Prod.fst he
  have hj : (t j).1≤u.1+(t u.2).1 :=
    (show (t j).1≤a+(t j).1 from le_add_left le_rfl).trans hsum.le
  have hi : (t u.2).1≤u.1+(t u.2).1 := le_add_left le_rfl
  exact ⟨j,hij,hpos,⟨rfl,tsub_le_iff_right.mpr (sup_le hi hj)⟩⟩

end
end Decoupling.HighDim.SchreyerSyzygy
