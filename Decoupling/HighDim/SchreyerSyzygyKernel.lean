import Decoupling.HighDim.SchreyerSyzygyCancellation
import Decoupling.HighDim.SchreyerGroebnerDivision

/-!
# Finite Schreyer pairs generate the entire actual kernel

The intermediate theorem packages one proved syzygy for each same-position
pair. Its leading divisibility statement follows from actual cancellation
in the column map, so neither kernel generation nor a kernel Gröbner-basis
certificate is an input. The S-pair standard-representation construction
will discharge the individual pair-witness premise.
-/
namespace Decoupling.HighDim.SchreyerSyzygy
open SchreyerModule
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D r s : ℕ}

def PairIndex (t : Fin s → Term D r) :=
  {ij : Fin s × Fin s // ij.1 < ij.2 ∧ (t ij.1).2=(t ij.2).2}

instance (t : Fin s → Term D r) : Fintype (PairIndex t) :=
  inferInstanceAs (Fintype {ij : Fin s × Fin s // ij.1 < ij.2 ∧ (t ij.1).2=(t ij.2).2})

def pairLeading (t : Fin s → Term D r) (i j : Fin s) : Term D s :=
  (((t i).1 ⊔ (t j).1)-(t i).1,i)

/-- The finite list consists of actual pair syzygies, and its leading terms
are the actual lcm quotients, including the empty-pair case. -/
theorem kernel_groebner_of_pair_witness
    (o : ModuleOrder D r) (G : Fin s → Vec K D r) (t : Fin s → Term D r)
    (hG : ∀ i,IsLeading o (G i) (t i))
    (hp : ∀ i j,i<j → (t i).2=(t j).2 →
      ∃ z : Vec K D s,columnMap G z=0 ∧
        IsLeading (inducedOrder o t) z (pairLeading t i j)) :
    ∃ n : ℕ, ∃ S : Fin n → Vec K D s,
      IsGroebnerBasis (inducedOrder o t) S (LinearMap.ker (columnMap G)) ∧
      (∀ a, ∃ i j,i<j ∧ (t i).2=(t j).2 ∧
        IsLeading (inducedOrder o t) (S a) (pairLeading t i j)) := by
  classical
  have hex (p : PairIndex t) : ∃ z : Vec K D s,columnMap G z=0 ∧
      IsLeading (inducedOrder o t) z (pairLeading t p.val.1 p.val.2) :=
    hp p.val.1 p.val.2 p.property.1 p.property.2
  choose z hz hlead using hex
  let e : Fin (Fintype.card (PairIndex t)) ≃ PairIndex t := (Fintype.equivFin _).symm
  refine ⟨Fintype.card (PairIndex t),fun a => z (e a),?_,?_⟩
  · refine ⟨fun a => hz (e a),?_⟩
    intro f hf u hu
    have hc : coeff (columnMap G f) (weight t u)=0 := by
      change columnMap G f=0 at hf
      rw [hf,coeff_zero]
    obtain ⟨j,hij,hpos,hdiv⟩ := pair_divides_of_image_coeff_zero G t hG hu hc
    let p : PairIndex t := ⟨(u.2,j),hij,hpos⟩
    refine ⟨e.symm p,pairLeading t u.2 j,?_,hdiv⟩
    simpa only [Equiv.apply_symm_apply] using hlead (e (e.symm p))
  · intro a
    exact ⟨(e a).val.1,(e a).val.2,(e a).property.1,(e a).property.2,hlead (e a)⟩

/-- A proved kernel GB supplies generation of the whole actual kernel. -/
theorem kernel_span_of_groebner {o : ModuleOrder D r} {G : Fin s → Vec K D r}
    {t : Fin s → Term D r} {n : ℕ} {S : Fin n → Vec K D s}
    (hS : IsGroebnerBasis (inducedOrder o t) S (LinearMap.ker (columnMap G))) :
    Submodule.span (Poly K D) (Set.range S)=LinearMap.ker (columnMap G) := hS.span_eq

end
end Decoupling.HighDim.SchreyerSyzygy
