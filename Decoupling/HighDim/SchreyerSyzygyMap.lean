import Decoupling.HighDim.SchreyerSyzygyOrder
import Decoupling.HighDim.SchreyerModuleProduct

/-! # The actual polynomial column map and its weighted leading bounds -/
namespace Decoupling.HighDim.SchreyerSyzygy
open SchreyerModule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D r s : ℕ}

def columnMap (G : Fin s → Vec K D r) : Vec K D s →ₗ[Poly K D] Vec K D r where
  toFun z := ∑ i,z i • G i
  map_add' z w := by simp only [Pi.add_apply,add_smul,Finset.sum_add_distrib]
  map_smul' a z := by simp only [Pi.smul_apply,smul_smul,Finset.smul_sum,RingHom.id_apply,smul_eq_mul]

@[simp] theorem columnMap_apply (G : Fin s → Vec K D r) (z : Vec K D s) :
    columnMap G z=∑ i,z i • G i := rfl

theorem coeff_sum {I : Type*} (f : I → Vec K D r) (s : Finset I) (t : Term D r) :
    coeff (∑ i∈s,f i) t = ∑ i∈s,coeff (f i) t := by
  simp only [coeff,Finset.sum_apply,MvPolynomial.coeff_sum]

theorem columnMap_coeff (G : Fin s → Vec K D r) (z : Vec K D s) (t : Term D r) :
    coeff (columnMap G z) t=∑ i,coeff (z i • G i) t :=
  coeff_sum _ _ _

@[simp] theorem columnMap_monomial (G : Fin s → Vec K D r) (a : Exponent D) (i : Fin s) (c : K) :
    columnMap G (monomial (a,i) c) = (MvPolynomial.monomial a c : Poly K D) • G i := by
  classical
  simp [columnMap,monomial,Pi.single_apply]

/-- Source term bounds control every actual product, without assuming G is GB. -/
theorem products_bounded {o : ModuleOrder D r} (G : Fin s → Vec K D r)
    (t : Fin s → Term D r) (hG : ∀ i,IsLeading o (G i) (t i))
    {z : Vec K D s} {u : Term D s} (hz : Bounded (inducedOrder o t) z u) (i : Fin s) :
    Bounded o (z i • G i) (weight t u) := by
  classical
  have he : z i • G i=∑ a∈(z i).support,(MvPolynomial.monomial a ((z i).coeff a) : Poly K D) • G i := by
    conv_lhs => rw [(z i).as_sum]
    rw [Finset.sum_smul]
  rw [he]
  apply bounded_sum
  intro a ha
  apply bounded_mono (bounded_monomial_smul (hG i).2 a ((z i).coeff a))
  exact weight_le_of_induced_le o t (hz (a,i) (MvPolynomial.mem_support_iff.mp ha))

theorem columnMap_bounded {o : ModuleOrder D r} (G : Fin s → Vec K D r)
    (t : Fin s → Term D r) (hG : ∀ i,IsLeading o (G i) (t i))
    {z : Vec K D s} {u : Term D s} (hz : Bounded (inducedOrder o t) z u) :
    Bounded o (columnMap G z) (weight t u) :=
  bounded_sum Finset.univ (fun i => z i • G i) (weight t u)
    (fun i _ => products_bounded G t hG hz i)

/-- The selected source leading coordinate contributes a genuinely nonzero
coefficient at its weighted image term. -/
theorem principal_product_leading {o : ModuleOrder D r} (G : Fin s → Vec K D r)
    (t : Fin s → Term D r) (hG : ∀ i,IsLeading o (G i) (t i))
    {z : Vec K D s} {u : Term D s} (hz : IsLeading (inducedOrder o t) z u) :
    IsLeading o (z u.2 • G u.2) (weight t u) := by
  have hzi : z u.2≠0 := by
    intro he
    exact hz.1 (by simp [coeff,he])
  have he : o.scalarOrder.degree (z u.2)=u.1 := hz.component_degree
  have hp := (hG u.2).polynomial_smul (z u.2) hzi
  rw [he] at hp
  exact hp

end
end Decoupling.HighDim.SchreyerSyzygy
