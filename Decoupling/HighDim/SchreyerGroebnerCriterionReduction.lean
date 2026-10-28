import Decoupling.HighDim.SchreyerGroebnerCriterionMinimal

/-! # A genuine kernel leading term lowers a coefficient preimage -/
namespace Decoupling.HighDim.SchreyerModule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D r s : ℕ}

theorem lower_preimage_of_kernel_leading (G : Fin s → Vec K D r) (io : ModuleOrder D s)
    {q z : Vec K D s} {u v : Term D s}
    (hq : IsLeading io q u) (hz : IsLeading io z v)
    (hker : (∑ i,z i • G i)=0) (hdiv : Divides v u) :
    ∃ q' : Vec K D s, (∑ i,q' i • G i)=(∑ i,q i • G i) ∧ StrictlyBelow io q' u := by
  obtain ⟨a,c,_,hb⟩ := cancel_leading hq hz hdiv
  let p : Poly K D := MvPolynomial.monomial a c
  refine ⟨q-p • z,?_,hb⟩
  calc
    (∑ i,(q-p • z) i • G i) = (∑ i,q i • G i)-p • (∑ i,z i • G i) := by
      simp only [Pi.sub_apply,Pi.smul_apply,smul_eq_mul,sub_smul,
        ← smul_smul,Finset.sum_sub_distrib,Finset.smul_sum]
    _ = ∑ i,q i • G i := by rw [hker,smul_zero,sub_zero]

end
end Decoupling.HighDim.SchreyerModule
