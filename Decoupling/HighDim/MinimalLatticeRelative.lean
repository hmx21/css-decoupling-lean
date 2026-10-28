import Decoupling.HighDim.MinimalLatticeForms

/-!
# Relative minimal indices inside an arbitrary retained lattice

Source: Proposition 1 of HD008. `Λ` may be skew: coordinates are an
actual additive equivalence, and final subgroups live in the original
integer translation lattice. The exponent gives the relative index in
Λ; the absolute index additionally contains Λ.index.
-/

namespace Decoupling.HighDim.MinimalLattice
noncomputable section

variable {p D : ℕ} [Fact p.Prime]
  (Λ : AddSubgroup (Translation D)) (e : Λ ≃+ Translation D)

/-- Express an original-lattice subgroup in the chosen coordinates of Λ. -/
def coordinateSubgroup (Γ : AddSubgroup (Translation D)) :
    AddSubgroup (Translation D) := (Γ.addSubgroupOf Λ).map e.toAddMonoidHom

@[simp] theorem coordinateSubgroup_index (Γ : AddSubgroup (Translation D)) :
    (coordinateSubgroup Λ e Γ).index = Γ.relIndex Λ := by
  exact AddSubgroup.index_map_equiv _ e

/-- Return a coordinate subgroup to its actual position inside Λ. -/
def embedSubgroup (H : AddSubgroup (Translation D)) : AddSubgroup (Translation D) :=
  (H.comap e.toAddMonoidHom).map Λ.subtype

theorem embedSubgroup_le (H : AddSubgroup (Translation D)) : embedSubgroup Λ e H ≤ Λ := by
  rintro a ⟨b, _, rfl⟩
  exact b.property

@[simp] theorem coordinateSubgroup_embed (H : AddSubgroup (Translation D)) :
    coordinateSubgroup Λ e (embedSubgroup Λ e H) = H := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨c, hc, hcb⟩ := hb
    have heq : c = b := Subtype.ext hcb
    change e c ∈ H at hc
    exact heq ▸ hc
  · intro ha
    refine ⟨e.symm a, ?_, e.apply_symm_apply a⟩
    exact ⟨e.symm a, by simpa using ha, rfl⟩

@[simp] theorem embedSubgroup_relIndex (H : AddSubgroup (Translation D)) :
    (embedSubgroup Λ e H).relIndex Λ = H.index := by
  rw [← coordinateSubgroup_index Λ e, coordinateSubgroup_embed]

theorem embedSubgroup_index (H : AddSubgroup (Translation D)) :
    (embedSubgroup Λ e H).index = H.index * Λ.index := by
  rw [embedSubgroup, AddSubgroup.index_map_subtype,
    AddSubgroup.index_comap_of_surjective H e.surjective]

instance embedSubgroup_finiteIndex [Λ.FiniteIndex]
    (H : AddSubgroup (Translation D)) [H.FiniteIndex] :
    (embedSubgroup Λ e H).FiniteIndex where
  index_ne_zero := by
    rw [embedSubgroup_index]
    exact mul_ne_zero AddSubgroup.FiniteIndex.index_ne_zero AddSubgroup.FiniteIndex.index_ne_zero

variable {ι : Type*} (degree : ι → ℕ) (Value : ι → Type*)
  [∀ i, AddCommGroup (Value i)] [∀ i, Module (ZMod p) (Value i)]
  (forms : ∀ i, AlternatingMap (ZMod p) (Residue p D) (Value i) (Fin (degree i)))

/-- Exact relative index, attained by an actual subgroup of the original Λ. -/
theorem relativeMinimum_attained [Λ.FiniteIndex] (positive : ∀ i, 0 < degree i) :
    ∃ Γ : AddSubgroup (Translation D), Γ ≤ Λ ∧ Γ.FiniteIndex ∧
      VanishesOn degree Value forms (image p D (coordinateSubgroup Λ e Γ)) ∧
      Γ.relIndex Λ = p ^ minimumCodim degree Value forms positive ∧
      Γ.index = p ^ minimumCodim degree Value forms positive * Λ.index := by
  obtain ⟨H, hfin, hH, hind⟩ := minimumIndex_attained degree Value forms positive
  let := hfin
  refine ⟨embedSubgroup Λ e H, embedSubgroup_le Λ e H, inferInstance, ?_, ?_, ?_⟩
  · simpa using hH
  · simpa using hind
  · rw [embedSubgroup_index, hind]

theorem relativeMinimum_le (positive : ∀ i, 0 < degree i)
    (Γ : AddSubgroup (Translation D)) [Γ.FiniteIndex]
    (hΓ : VanishesOn degree Value forms (image p D (coordinateSubgroup Λ e Γ))) :
    p ^ minimumCodim degree Value forms positive ≤ Γ.relIndex Λ := by
  let : (coordinateSubgroup Λ e Γ).FiniteIndex := by
    constructor
    rw [coordinateSubgroup_index]
    exact ne_zero_of_dvd_ne_zero AddSubgroup.FiniteIndex.index_ne_zero
      (AddSubgroup.relIndex_dvd_index_of_normal Γ Λ)
  simpa using minimumIndex_le degree Value forms positive (coordinateSubgroup Λ e Γ) hΓ

theorem relativeMinimum_isLeast [Λ.FiniteIndex] (positive : ∀ i, 0 < degree i) :
    IsLeast {n : ℕ | ∃ Γ : AddSubgroup (Translation D), Γ ≤ Λ ∧ Γ.FiniteIndex ∧
      VanishesOn degree Value forms (image p D (coordinateSubgroup Λ e Γ)) ∧
      Γ.relIndex Λ = n} (p ^ minimumCodim degree Value forms positive) := by
  obtain ⟨Γ, hle, hfin, hΓ, hind, _⟩ := relativeMinimum_attained Λ e degree Value forms positive
  refine ⟨⟨Γ, hle, hfin, hΓ, hind⟩, ?_⟩
  rintro n ⟨Γ', _, hfin', hΓ', rfl⟩
  let := hfin'
  exact relativeMinimum_le Λ e degree Value forms positive Γ' hΓ'

end
end Decoupling.HighDim.MinimalLattice
