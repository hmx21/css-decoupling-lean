import Decoupling.HighDim.DecouplingCriterionMultiplicity
import Decoupling.HighDim.CorollaryOne
import Decoupling.HighDim.TwoLayerThree

/-!
# HD010 Corollaries 1 and 2 with the unrestricted physical predicate

The manuscript's “can be decoupled” means existence of some finite toric
stack. Its equivalence to the original native multiplicities is proved,
so the earlier coarse-graining and minimum results retain their meaning.
-/
namespace Decoupling.HighDim.Paper
open CategoryTheory DecouplingCriterion
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {p D q s r : ℕ} [Fact p.Prime]
  (c : CSS.Checks (ZMod p) D q s r)

/-- Corollary 1: both the actual derived splitting and actual physical
decoupling on exactly p^(m−1) Λ_triv, from the original assumptions. -/
theorem corollary1_X (h : Layers.FiniteXLayers c) (hc : c.Topological) (hD : 2 ≤ D) :
    let := TheoremOne.lattice_finiteIndex c h
    Nonempty (TheoremOne.restrictedProfile c h ≅ TheoremOne.target c) ∧
      DecouplesOn (TheoremOne.lattice c) (TheoremOne.coordinates c h) c := by
  let := TheoremOne.lattice_finiteIndex c h
  exact ⟨TheoremOne.split c h hc hD,
    ⟨SplitMultiplicity.multiplicities c, CorollaryOne.decouples_X c h hc hD⟩⟩

/-- Corollary 1 in the Z sector, on the lattice determined by that entire
sector, with the actual Fourier-dual physical target. -/
theorem corollary1_Z (h : Layers.FiniteZLayers c) (hc : c.Topological) (hD : 2 ≤ D) :
    let := TheoremOne.lattice_finiteIndex c.swap h
    Nonempty (TheoremOne.restrictedProfile c.swap h ≅ TheoremOne.target c.swap) ∧
      DecouplesOnZ (TheoremOne.lattice c.swap) (TheoremOne.coordinates c.swap h) c := by
  let := TheoremOne.lattice_finiteIndex c.swap h
  have hs := TheoremOne.split c.swap h (c.topological_swap hc) hD
  refine ⟨hs, (theorem1_Z _ _ c hc).mpr ?_⟩
  exact ⟨SplitMultiplicity.multiplicities c.swap, hs⟩

variable (Λ : AddSubgroup (Translation D)) [Λ.FiniteIndex] (e : Λ ≃+ Translation D)
  (h : Layers.FiniteXLayers c) (hc : c.Topological) (hD : 1 ≤ D)

/-- The two-layer native class is the sole obstruction after necessity of
the common translation kernel has been established. -/
theorem corollary2_twoLayers (i j : ℤ) (hij : i < j) (hs : Profile.support c = {i, j}) :
    DecouplesOn Λ e c ↔ ∃ hΛ : Λ ≤ Translations.lambda0 c,
      (TwoLayer.canonicalGluing c h hc hD i j hij hs).mapExactFunctor
        (TwoLayer.fromKernelRestriction Λ e c h hΛ) = 0 := by
  rw [decouples_iff_original_multiplicities Λ e c hc hD h]
  exact TwoLayer.decouplesOn_iff_kernel_and_nativeGluing Λ e c h hc hD i j hij hs

/-- The same obstruction as its actual Hom-valued alternating form on
the mod-p image of the subgroup, exactly as in Corollary 2. -/
theorem corollary2_form (i j : ℤ) (hij : i < j) (hs : Profile.support c = {i, j}) :
    DecouplesOn Λ e c ↔ Λ ≤ Translations.lambda0 c ∧
      ∀ v : Fin (j - i + 1).toNat → MinimalLattice.Residue p D,
        (∀ k, v k ∈ MinimalLattice.image p D
          (MinimalLattice.coordinateSubgroup (Translations.lambda0 c)
            (TrivialLayers.lambda0Coordinates c h) Λ)) →
        TwoLayer.canonicalForm c h hc hD i j hij hs v = 0 := by
  rw [decouples_iff_original_multiplicities Λ e c hc hD h]
  constructor
  · intro hd
    have hΛ := TwoLayer.decouplesOn_le_lambda0 Λ e c hd
    exact ⟨hΛ, (TwoLayer.decouplesOn_iff_form_vanishes c h hc hD i j hij hs Λ e hΛ).mp hd⟩
  · rintro ⟨hΛ, hv⟩
    exact (TwoLayer.decouplesOn_iff_form_vanishes c h hc hD i j hij hs Λ e hΛ).mpr hv

include h hc hD in
theorem corollary2_atMostOne (hm : Layers.nonzeroLayerCount c ≤ 1) :
    DecouplesOn Λ e c ↔ Λ ≤ Translations.lambda0 c := by
  rw [decouples_iff_original_multiplicities Λ e c hc hD h]
  exact TwoLayer.decouplesOn_iff_commonKernel_of_atMostOne Λ e c h hc hD hm

/-- Candidate indices quantify actual physical decouplings onto any toric
stack; the index is relative to the original common translation kernel. -/
def DecouplingIndices : Set ℕ := {n | ∃ (Γ : AddSubgroup (Translation D)) (hfin : Γ.FiniteIndex),
  @DecouplesOn p D q s r _ Γ hfin (@LatticeBasis.coordinates D Γ hfin) c ∧
    Γ.relIndex (Translations.lambda0 c) = n}

omit [Λ.FiniteIndex] in
include h hc hD in
theorem decouplingIndices_eq : DecouplingIndices c = TwoLayer.DecouplingIndices c := by
  ext n
  constructor
  · rintro ⟨Γ, hfin, hd, hn⟩
    let := hfin
    exact ⟨Γ, hfin, (decouples_iff_original_multiplicities Γ _ c hc hD h).mp hd, hn⟩
  · rintro ⟨Γ, hfin, hd, hn⟩
    let := hfin
    exact ⟨Γ, hfin, (decouples_iff_original_multiplicities Γ _ c hc hD h).mpr hd, hn⟩

end

section Three
open DecouplingCriterion
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
variable {p q s r : ℕ} [Fact p.Prime] (c : CSS.Checks (ZMod p) 3 q s r)
  (h : Layers.FiniteXLayers c) (hc : c.Topological)

/-- Corollary 2's complete three-dimensional classification, now expressed
using existential actual toric targets rather than fixed multiplicities. -/
theorem corollary2_threeDimensional : IsLeast (DecouplingIndices c)
    (if ∀ i, TwoLayer.threeCoefficients c h hc i = 0 then 1 else
      if LinearIndependent (ZMod p) (TwoLayer.threeCoefficients c h hc) then p ^ 2 else p) := by
  rw [decouplingIndices_eq c h hc (by decide)]
  exact TwoLayer.threeDimensional_minimumIndex c h hc

end
end Three
end Decoupling.HighDim.Paper
