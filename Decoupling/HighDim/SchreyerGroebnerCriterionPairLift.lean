import Decoupling.HighDim.SchreyerSyzygyMap
import Decoupling.HighDim.SchreyerSyzygyPair

/-!
# A real normalized S-pair lift, without a Gröbner premise

An actual strict standard representation supplies the correction vector.
The resulting source vector lies in the actual column-map kernel and has
the stated leading term in the induced Schreyer order. This common lemma
is used both by the Buchberger criterion and by the syzygy construction.
-/
namespace Decoupling.HighDim.SchreyerSyzygy
open SchreyerModule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D r s : ℕ}

def pairLift (G : Fin s → Vec K D r) (t : Fin s → Term D r)
    (i j : Fin s) (q : Vec K D s) : Vec K D s :=
  monomial (((t i).1 ⊔ (t j).1)-(t i).1,i) (coeff (G i) (t i))⁻¹ -
    monomial (((t i).1 ⊔ (t j).1)-(t j).1,j) (coeff (G j) (t j))⁻¹ - q

theorem pairLift_map (G : Fin s → Vec K D r) (t : Fin s → Term D r)
    (i j : Fin s) (q : Vec K D s) :
    columnMap G (pairLift G t i j q) = sPolynomial (G i) (G j) (t i) (t j) - columnMap G q := by
  simp only [pairLift,map_sub,columnMap_monomial,sPolynomial]

theorem pairLift_kernel (G : Fin s → Vec K D r) (t : Fin s → Term D r)
    (i j : Fin s) (q : Vec K D s)
    (he : sPolynomial (G i) (G j) (t i) (t j) = columnMap G q) :
    columnMap G (pairLift G t i j q) = 0 := by rw [pairLift_map,he,sub_self]

theorem correction_below_pair {o : ModuleOrder D r}
    (G : Fin s → Vec K D r) (t : Fin s → Term D r) (hG : ∀ k,IsLeading o (G k) (t k))
    (i j : Fin s) (q : Vec K D s)
    (hb : ∀ k,StrictlyBelow o (q k • G k) (pairTop (t i) (t j))) :
    StrictlyBelow (inducedOrder o t) q (((t i).1 ⊔ (t j).1)-(t i).1,i) := by
  intro u hu
  apply induced_lt_of_weight_lt o t
  change o.LT (shift u.1 (t u.2))
    (shift (((t i).1 ⊔ (t j).1)-(t i).1) (t i))
  rw [pairTop_left]
  exact polynomial_smul_below_coeff (hG u.2) (hb u.2) u.1 hu

private theorem below_coeff_self (o : ModuleOrder D r) {v : Vec K D r} {u : Term D r}
    (h : StrictlyBelow o v u) : coeff v u = 0 := by
  by_contra hn
  exact (@lt_irrefl _ o.termOrder.toPreorder u) (h u hn)

theorem pairLift_leading {o : ModuleOrder D r}
    (G : Fin s → Vec K D r) (t : Fin s → Term D r) (hG : ∀ k,IsLeading o (G k) (t k))
    (i j : Fin s) (hij : i<j) (hpos : (t i).2=(t j).2) (q : Vec K D s)
    (hb : ∀ k,StrictlyBelow o (q k • G k) (pairTop (t i) (t j))) :
    IsLeading (inducedOrder o t) (pairLift G t i j q)
      (((t i).1 ⊔ (t j).1)-(t i).1,i) := by
  let io := inducedOrder o t
  let u : Term D s := (((t i).1 ⊔ (t j).1)-(t i).1,i)
  let v : Term D s := (((t i).1 ⊔ (t j).1)-(t j).1,j)
  let left : Vec K D s := monomial u (coeff (G i) (t i))⁻¹
  let right : Vec K D s := monomial v (coeff (G j) (t j))⁻¹
  have hleft : IsLeading io left u := isLeading_monomial io u _ (inv_ne_zero (hG i).1)
  have hright : StrictlyBelow io right u :=
    below_of_bounded_of_lt (bounded_monomial io v _) (primary_pair_lt o t i j hij hpos)
  have hq : StrictlyBelow io q u := correction_below_pair G t hG i j q hb
  have hcr : coeff right u = 0 := below_coeff_self io hright
  have hcq : coeff q u = 0 := below_coeff_self io hq
  change IsLeading io (left-right-q) u
  refine ⟨?_,bounded_sub (bounded_sub hleft.2 (bounded_of_below hright)) (bounded_of_below hq)⟩
  simpa only [coeff_sub,hcr,hcq,sub_zero] using hleft.1

end
end Decoupling.HighDim.SchreyerSyzygy
