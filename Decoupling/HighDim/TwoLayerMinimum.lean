import Decoupling.HighDim.TwoLayerCriterion
import Decoupling.HighDim.MinimalLatticeNested

/-!
# Exact optimal physical decoupling lattice for two layers

The canonical native attachment is converted to its proved alternating
form. The index minimum is then over actual finite-index subgroups and
actual stable physical decouplings, not over surrogate split profiles.
-/

namespace Decoupling.HighDim.TwoLayer
open CategoryTheory CategoryTheory.Limits PostnikovInduction MinimalLattice
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {p D q s r : ℕ} [Fact p.Prime]
  (c : CSS.Checks (ZMod p) D q s r) (h : Layers.FiniteXLayers c)
  (hc : c.Topological) (hD : 1 ≤ D) (i j : ℤ) (hij : i < j)
  (hs : Profile.support c = {i, j})

abbrev GluingValue := Layers.coefficients (H (Lambda0Profile.profile c h) j) →ₗ[ZMod p]
  Layers.coefficients (H (Lambda0Profile.profile c h) i)

def canonicalForm : AlternatingMap (ZMod p) (Residue p D)
    (GluingValue c h i j) (Fin (j - i + 1).toNat) := by
  have hi : i ∈ Profile.support c := by rw [hs]; simp
  have hj : j ∈ Profile.support c := by rw [hs]; simp
  let := (Lambda0Profile.homology_trivialFinite c h j hj).2
  exact ExtValues.nativeAlternatingEquiv _ _
    (Lambda0Profile.homology_trivialFinite c h j hj).1
    (Lambda0Profile.homology_trivialFinite c h i hi).1 _
      (canonicalGluing c h hc hD i j hij hs)

theorem decouplesOn_iff_form_vanishes (Γ : AddSubgroup (Translation D)) [Γ.FiniteIndex]
    (e : Γ ≃+ Translation D) (hΓ : Γ ≤ Translations.lambda0 c) :
    DecouplesOn Γ e c ↔
      ∀ v : Fin (j - i + 1).toNat → Residue p D,
        (∀ k, v k ∈ image p D (coordinateSubgroup (Translations.lambda0 c)
          (TrivialLayers.lambda0Coordinates c h) Γ)) → canonicalForm c h hc hD i j hij hs v = 0 := by
  rw [decouplesOn_iff_nativeGluing_zero Γ e c h hc hD i j hij hs hΓ]
  have hi : i ∈ Profile.support c := by rw [hs]; simp
  have hj : j ∈ Profile.support c := by rw [hs]; simp
  let := (Lambda0Profile.homology_trivialFinite c h j hj).2
  have he := KoszulLattice.finite_restriction_eq_zero_iff_image
    (nestedCoordinateMap (Translations.lambda0 c) Γ hΓ (TrivialLayers.lambda0Coordinates c h) e)
    (H (Lambda0Profile.profile c h) j) (H (Lambda0Profile.profile c h) i)
    (Lambda0Profile.homology_trivialFinite c h j hj).1
    (Lambda0Profile.homology_trivialFinite c h i hi).1 _ (canonicalGluing c h hc hD i j hij hs)
  rw [nested_reducedMap_image] at he
  exact he

def DecouplingIndices : Set ℕ := {n | ∃ (Γ : AddSubgroup (Translation D)) (hfin : Γ.FiniteIndex),
  @DecouplesOn p D q s r _ Γ hfin (@LatticeBasis.coordinates D Γ hfin) c ∧
    Γ.relIndex (Translations.lambda0 c) = n}

def canonicalMinimumCodim : ℕ := minimumCodim (fun _ : Unit => (j - i + 1).toNat)
  (fun _ => GluingValue c h i j) (fun _ => canonicalForm c h hc hD i j hij hs)
    (fun _ => by omega)

/-- Exact minimum, including an attaining actual lattice and a lower bound
against every physical decoupling lattice. -/
theorem decoupling_minimumIndex : IsLeast (DecouplingIndices c)
    (p ^ canonicalMinimumCodim c h hc hD i j hij hs) := by
  let := Translations.lambda0_finiteIndex c h
  have he : DecouplingIndices c = {n : ℕ | ∃ Γ : AddSubgroup (Translation D),
      Γ ≤ Translations.lambda0 c ∧ Γ.FiniteIndex ∧
      VanishesOn (fun _ : Unit => (j - i + 1).toNat) (fun _ => GluingValue c h i j)
        (fun _ => canonicalForm c h hc hD i j hij hs)
        (image p D (coordinateSubgroup (Translations.lambda0 c) (TrivialLayers.lambda0Coordinates c h) Γ)) ∧
          Γ.relIndex (Translations.lambda0 c) = n} := by
    ext n
    constructor
    · rintro ⟨Γ, hfin, hd, hn⟩
      let := hfin
      have hΓ := decouplesOn_le_lambda0 Γ (LatticeBasis.coordinates Γ) c hd
      exact ⟨Γ, hΓ, hfin, fun _ => (decouplesOn_iff_form_vanishes c h hc hD i j hij hs
        Γ (LatticeBasis.coordinates Γ) hΓ).mp hd, hn⟩
    · rintro ⟨Γ, hΓ, hfin, hv, hn⟩
      let := hfin
      exact ⟨Γ, hfin, (decouplesOn_iff_form_vanishes c h hc hD i j hij hs
        Γ (LatticeBasis.coordinates Γ) hΓ).mpr (hv ()), hn⟩
  rw [he]
  exact relativeMinimum_isLeast (Translations.lambda0 c) (TrivialLayers.lambda0Coordinates c h)
    _ _ _ _

include h hc hD in
/-- At most one genuine layer: Λ₀ itself is an optimal physical lattice. -/
theorem decoupling_minimumIndex_of_atMostOne (hm : Layers.nonzeroLayerCount c ≤ 1) :
    IsLeast (DecouplingIndices c) 1 := by
  let := Translations.lambda0_finiteIndex c h
  refine ⟨?_, ?_⟩
  · refine ⟨Translations.lambda0 c, inferInstance, ?_, AddSubgroup.relIndex_self _⟩
    exact (decouplesOn_iff_commonKernel_of_atMostOne (Translations.lambda0 c)
      (LatticeBasis.coordinates _) c h hc hD hm).mpr le_rfl
  · rintro n ⟨Γ, hfin, _, rfl⟩
    let := hfin
    exact Nat.one_le_iff_ne_zero.mpr (ne_zero_of_dvd_ne_zero
      AddSubgroup.FiniteIndex.index_ne_zero (AddSubgroup.relIndex_dvd_index_of_normal Γ _))

end
end Decoupling.HighDim.TwoLayer
