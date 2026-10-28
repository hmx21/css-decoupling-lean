import Decoupling.HighDim.SchreyerGroebnerCriterionFamily
import Decoupling.HighDim.SchreyerModuleProduct
import Decoupling.HighDim.SchreyerSyzygyOrder

/-!
# The well-founded minimal-preimage part of the module Gröbner criterion

The auxiliary lowering hypothesis below is discharged by actual S-pair
syzygies in the final criterion; it is not a final code or GB assumption.
No Gröbner property is used in this minimal-preimage argument.
-/
namespace Decoupling.HighDim.SchreyerModule
noncomputable section
open SchreyerSyzygy
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type*} [Field K] {D r s : ℕ}

theorem bounded_image_of_induced_bound (o : ModuleOrder D r)
    (G : Fin s → Vec K D r) (t : Fin s → Term D r)
    (hG : ∀ i, Bounded o (G i) (t i)) {q : Vec K D s} {u : Term D s}
    (hq : Bounded (inducedOrder o t) q u) :
    Bounded o (∑ i, q i • G i) (weight t u) := by
  apply bounded_sum
  intro i _
  by_cases hz : q i = 0
  · simpa only [hz,zero_smul] using bounded_zero (K := K) o (weight t u)
  have hc : coeff q (o.scalarOrder.degree (q i),i) ≠ 0 :=
    o.scalarOrder.coeff_degree_ne_zero_iff.mpr hz
  exact bounded_mono (bounded_polynomial_smul (hG i) (q i))
    (weight_le_of_induced_le o t (hq _ hc))

theorem isGroebnerBasis_of_preimage_lowering (o : ModuleOrder D r)
    (G : Fin s → Vec K D r) (t : Fin s → Term D r)
    (hG : ∀ i, IsLeading o (G i) (t i))
    (lower : ∀ (q : Vec K D s) (u : Term D s), IsLeading (inducedOrder o t) q u →
      coeff (∑ i, q i • G i) (weight t u) = 0 →
      ∃ q' : Vec K D s, (∑ i, q' i • G i) = (∑ i, q i • G i) ∧
        StrictlyBelow (inducedOrder o t) q' u) :
    IsGroebnerBasis o G (Submodule.span (Poly K D) (Set.range G)) := by
  classical
  refine ⟨fun i => Submodule.subset_span ⟨i,rfl⟩,?_⟩
  intro f hf tf htf
  obtain ⟨q₀,hq₀⟩ := (Submodule.mem_span_range_iff_exists_fun (Poly K D)).mp hf
  have hn₀ : q₀ ≠ 0 := by
    intro he
    apply htf.ne_zero
    rw [← hq₀,he]
    simp
  let io := inducedOrder o t
  let S : Set (Term D s) := {u | ∃ q : Vec K D s, IsLeading io q u ∧ (∑ i,q i • G i)=f}
  have hS : S.Nonempty := ⟨lm io q₀ hn₀,q₀,lm_isLeading io q₀ hn₀,hq₀⟩
  obtain ⟨u,⟨q,hq,he⟩,hmin⟩ := io.wellFounded.has_min S hS
  have hc : coeff (∑ i,q i • G i) (weight t u) ≠ 0 := by
    intro hz
    obtain ⟨q',he',hb⟩ := lower q u hq hz
    have hrep : (∑ i,q' i • G i)=f := he'.trans he
    have hq' : q' ≠ 0 := by
      intro hz'
      apply htf.ne_zero
      rw [← hrep,hz']
      simp
    exact hmin (lm io q' hq') ⟨q',lm_isLeading io q' hq',hrep⟩
      ((below_iff_lm_lt io q' hq' u).mp hb)
  have hb := bounded_image_of_induced_bound o G t (fun i => (hG i).2) hq.2
  rw [he] at hc hb
  have hw : weight t u = tf :=
    @le_antisymm _ o.termOrder.toPartialOrder _ _ (htf.2 _ hc) (hb _ htf.1)
  refine ⟨u.2,t u.2,hG u.2,?_⟩
  exact (divides_iff_shift _ _).mpr ⟨u.1,hw⟩

end
end Decoupling.HighDim.SchreyerModule
