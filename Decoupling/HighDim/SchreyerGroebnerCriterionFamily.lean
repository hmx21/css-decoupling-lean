import Decoupling.HighDim.SchreyerGroebnerCompletion

/-!
# Removing zero generators for the module Buchberger criterion

The reduction keeps the actual nonzero members, their polynomial span and
every strict S-pair representation. It does not presume the Gröbner property.
All-zero families become the empty family.
-/
namespace Decoupling.HighDim.SchreyerModule
noncomputable section
open SchreyerSyzygy
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {D r s n : ℕ}

theorem exists_nonzero_subfamily (G : Fin s → Vec K D r) :
    ∃ n : ℕ, ∃ index : Fin n → Fin s, Function.Injective index ∧
      (∀ j, G (index j) ≠ 0) ∧ (∀ i, G i ≠ 0 → ∃ j, index j = i) := by
  classical
  let J := {i : Fin s // G i ≠ 0}
  let e : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J,fun j => (e j).val,?_,fun j => (e j).property,?_⟩
  · intro i j he
    exact e.injective (Subtype.ext he)
  · intro i hi
    refine ⟨e.symm ⟨i,hi⟩,?_⟩
    simp

theorem sum_nonzero_subfamily (G : Fin s → Vec K D r) (index : Fin n → Fin s)
    (hi : Function.Injective index) (hcover : ∀ i, G i ≠ 0 → ∃ j, index j = i)
    (q : Fin s → Poly K D) :
    (∑ i, q i • G i) = ∑ j, q (index j) • G (index j) := by
  classical
  calc
    (∑ i, q i • G i) = ∑ i ∈ Finset.univ.image index, q i • G i := by
      apply (Finset.sum_subset (Finset.subset_univ _ ) ?_).symm
      intro i _ hnot
      have hz : G i = 0 := by
        by_contra hn
        obtain ⟨j,hj⟩ := hcover i hn
        exact hnot (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩)
      simp [hz]
    _ = ∑ j, q (index j) • G (index j) :=
      Finset.sum_image (fun i _ j _ he => hi he)

theorem span_nonzero_subfamily (G : Fin s → Vec K D r) (index : Fin n → Fin s)
    (hcover : ∀ i, G i ≠ 0 → ∃ j, index j = i) :
    Submodule.span (Poly K D) (Set.range (fun j => G (index j))) =
      Submodule.span (Poly K D) (Set.range G) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨j,rfl⟩
    exact Submodule.subset_span ⟨index j,rfl⟩
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    by_cases hz : G i = 0
    · rw [hz]
      exact Submodule.zero_mem _
    · obtain ⟨j,rfl⟩ := hcover i hz
      exact Submodule.subset_span ⟨j,rfl⟩

theorem ClosedPairs.nonzero_subfamily {o : ModuleOrder D r} {G : Fin s → Vec K D r}
    (hc : ClosedPairs o G) (index : Fin n → Fin s)
    (hi : Function.Injective index) (hcover : ∀ i, G i ≠ 0 → ∃ j, index j = i) :
    ClosedPairs o (fun j => G (index j)) := by
  intro i j u v hGi hGj hp
  obtain ⟨q,hq,hb⟩ := hc (index i) (index j) u v hGi hGj hp
  exact ⟨fun k => q (index k),hq.trans (sum_nonzero_subfamily G index hi hcover q),
    fun k => hb (index k)⟩

theorem IsGroebnerBasis.of_nonzero_subfamily {o : ModuleOrder D r}
    {G : Fin s → Vec K D r} (index : Fin n → Fin s)
    (hcover : ∀ i, G i ≠ 0 → ∃ j, index j = i)
    (hG : IsGroebnerBasis o (fun j => G (index j))
      (Submodule.span (Poly K D) (Set.range (fun j => G (index j))))) :
    IsGroebnerBasis o G (Submodule.span (Poly K D) (Set.range G)) := by
  refine ⟨fun i => Submodule.subset_span ⟨i,rfl⟩,?_⟩
  intro f hf t ht
  rw [← span_nonzero_subfamily G index hcover] at hf
  obtain ⟨j,u,hj,hd⟩ := hG.leading f hf t ht
  exact ⟨index j,u,hj,hd⟩

end
end Decoupling.HighDim.SchreyerModule
