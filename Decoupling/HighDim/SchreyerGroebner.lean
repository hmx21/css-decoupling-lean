import Decoupling.HighDim.SchreyerModuleArithmetic
import Mathlib.Order.Antichain

/-!
# Finite minimal module Gröbner bases exist, by Dickson's lemma

The definition uses actual leading-term divisibility inside the actual
submodule. Generation is not an input field: it follows later by division.
The present existence proof is mathematical and noncomputable. It is not
presented as an executable Buchberger implementation.
-/
namespace Decoupling.HighDim.SchreyerModule
noncomputable section
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D r s : ℕ}

structure IsGroebnerBasis (o : ModuleOrder D r) (G : Fin s → Vec K D r)
    (N : Submodule (Poly K D) (Vec K D r)) : Prop where
  mem : ∀ i, G i∈N
  leading : ∀ f∈N, ∀ t, IsLeading o f t →
    ∃ i u, IsLeading o (G i) u ∧ Divides u t

structure IsMinimal (o : ModuleOrder D r) (G : Fin s → Vec K D r) : Prop where
  nonzero : ∀ i,G i≠0
  minimal : ∀ i j u v, IsLeading o (G i) u → IsLeading o (G j) v → Divides u v → i=j

/-- An actual finite minimal leading-term basis, with no GB-existence premise. -/
theorem exists_minimal_groebner (o : ModuleOrder D r)
    (N : Submodule (Poly K D) (Vec K D r)) :
    ∃ s : ℕ, ∃ G : Fin s → Vec K D r, IsGroebnerBasis o G N ∧ IsMinimal o G := by
  classical
  let E (i : Fin r) : Set (Exponent D) := {a | ∃ f∈N,IsLeading o f (a,i)}
  have hfinite (i : Fin r) : {a : Exponent D | Minimal (· ∈ E i) a}.Finite :=
    WellQuasiOrderedLE.finite_of_isAntichain (setOfPred_minimal_antichain (· ∈ E i))
  let : ∀ i : Fin r, Fintype {a : Exponent D // Minimal (· ∈ E i) a} :=
    fun i => (hfinite i).fintype
  let J := (i : Fin r) × {a : Exponent D // Minimal (· ∈ E i) a}
  let term (j : J) : Term D r := (j.2.val,j.1)
  have hinj : Function.Injective term := by
    rintro ⟨i,a,ha⟩ ⟨j,b,hb⟩ he
    have hp : i=j := congrArg Prod.snd he
    subst j
    have hx : a=b := congrArg Prod.fst he
    subst b
    rfl
  have hex (j : J) : ∃ f : Vec K D r,f∈N ∧ IsLeading o f (term j) := j.2.property.1
  choose g hmem hlead using hex
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J,fun i => g (e i),?_,?_⟩
  · refine ⟨fun i => hmem (e i),?_⟩
    intro f hf t ht
    have hte : t.1∈E t.2 := ⟨f,hf,ht⟩
    obtain ⟨a,hat,hmin⟩ := (Set.isPWO_of_wellQuasiOrderedLE (E t.2)).exists_le_minimal hte
    let j : J := ⟨t.2,⟨a,hmin⟩⟩
    refine ⟨e.symm j,term j,?_,⟨rfl,hat⟩⟩
    simpa only [Equiv.apply_symm_apply] using hlead (e (e.symm j))
  · refine ⟨fun i => (hlead (e i)).ne_zero,?_⟩
    intro i j u v hu hv huv
    have he_u := isLeading_unique o (hlead (e i)) hu
    have he_v := isLeading_unique o (hlead (e j)) hv
    subst u
    subst v
    apply e.injective
    apply hinj
    have hpos : (e i).1=(e j).1 := huv.1
    have hai : (e i).2.val∈E (e j).1 := by
      rw [←hpos]
      exact (e i).2.property.1
    have hrev : (e j).2.val≤(e i).2.val := (e j).2.property.2 hai huv.2
    exact Prod.ext (le_antisymm huv.2 hrev) hpos

end
end Decoupling.HighDim.SchreyerModule
