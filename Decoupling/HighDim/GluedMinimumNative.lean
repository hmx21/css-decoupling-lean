import Decoupling.HighDim.GluedMinimumNativeLayers
import Decoupling.HighDim.GluedMinimumLattices
import Decoupling.HighDim.GluedRectangular
import Decoupling.HighDim.MinimalLatticeRestriction

/-!
# The literal example's physical minimum and all optimal lattices

The physical decoupling predicate uses the actual coarse checks and the
original native Ext multiplicities. Its lattice test is derived from the
actual cone gluing, rather than imposed as a definition of decoupling.
-/
namespace Decoupling.HighDim.Glued
open CategoryTheory CategoryTheory.Limits PostnikovInduction TrivialLayers
open MinimalLattice MinimalLattice.Three Koszul KoszulLattice
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable (K : Type) [Field K]

def restrictedHomologyOneIso (a : Translation 3 →+ Translation 3) :
    H ((ModuleCat.restrictScalars (latticeMap K a)).mapDerivedCategory.obj
      (Profile.S_X (checks K))) 1 ≅ coefficientModule K 3 :=
  ExactDerivedHomology.homologyIso _ _ 1 ≪≫
    (ModuleCat.restrictScalars (latticeMap K a)).mapIso (actualHomologyOneIso K) ≪≫
      (latticeCoefficientIso K a).symm

def restrictedHomologyTwoIso (a : Translation 3 →+ Translation 3) :
    H ((ModuleCat.restrictScalars (latticeMap K a)).mapDerivedCategory.obj
      (Profile.S_X (checks K))) 2 ≅ coefficientModule K 3 :=
  ExactDerivedHomology.homologyIso _ _ 2 ≪≫
    (ModuleCat.restrictScalars (latticeMap K a)).mapIso (actualHomologyTwoIso K) ≪≫
      (latticeCoefficientIso K a).symm

def restrictedHomologySumIso (a : Translation 3 →+ Translation 3) :
    TwoLayer.homologySum ((ModuleCat.restrictScalars (latticeMap K a)).mapDerivedCategory.obj
      (Profile.S_X (checks K))) {1, 2} ≅ twoCoefficientLayers K :=
  TwoLayer.pairSumIso _ 1 2 (by omega) ≪≫ biprod.mapIso
    ((DerivedCategory.singleFunctor _ 1).mapIso (restrictedHomologyOneIso K a))
    ((DerivedCategory.singleFunctor _ 2).mapIso (restrictedHomologyTwoIso K a))


theorem singlePlaquetteForm_apply (v : Fin 2 → Fin 3 → K) :
    form (![-1, 0, 0] : Fin 3 → K) v =
      -Matrix.det (fun i j => v i (plaquette 0 j)) := by
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, form_pair]
  simp [evaluate, minors, Fin.sum_univ_succ, Matrix.det_fin_two, plaquette]

/-- Equality of the actual native restriction and the explicit determinant
form. This uses the proved Koszul comparison, including its minus sign. -/
theorem couplingRestriction_iff_form (a : Translation 3 →+ Translation 3) :
    (couplingClass K).mapExactFunctor (ModuleCat.restrictScalars (latticeMap K a)) = 0 ↔
      (form (![-1, 0, 0] : Fin 3 → K)).compLinearMap (reducedMap K a) = 0 := by
  rw [couplingRestriction_iff_minor, ExtValues.alternating_eq_zero_iff_cell_values]
  apply forall_congr'
  intro J
  simp only [AlternatingMap.compLinearMap_apply, reducedMap_single, singlePlaquetteForm_apply,
    neg_eq_zero]

variable {p : ℕ} [Fact p.Prime]
  (Γ : AddSubgroup (Translation 3)) [Γ.FiniteIndex] (e : Γ ≃+ Translation 3)

def onLatticeHomologySumIso :
    TwoLayer.homologySum (TwoLayer.onLatticeProfile Γ e (checks (ZMod p))) {1, 2} ≅
      twoCoefficientLayers (ZMod p) := by
  unfold TwoLayer.onLatticeProfile TwoLayer.latticeRestriction
  simpa only [latticeMap_eq_coordinateEmbedding] using
    restrictedHomologySumIso (ZMod p) (inclusionCoordinates Γ e)

theorem decouplesOn_iff_couplingRestriction :
    TwoLayer.DecouplesOn Γ e (checks (ZMod p)) ↔
      (couplingClass (ZMod p)).mapExactFunctor
        (ModuleCat.restrictScalars (latticeMap (ZMod p) (inclusionCoordinates Γ e))) = 0 := by
  rw [TwoLayer.decouplesOn_iff_formal Γ e (checks (ZMod p)) (finiteXLayers p)
    (topological (ZMod p)) (by rw [lambda0_eq_top]; exact le_top), actualSupport]
  rw [← actualProfile_formal_iff]
  have he : Nonempty (TwoLayer.onLatticeProfile Γ e (checks (ZMod p)) ≅
      TwoLayer.homologySum (TwoLayer.onLatticeProfile Γ e (checks (ZMod p))) {1, 2}) ↔
      Nonempty (TwoLayer.onLatticeProfile Γ e (checks (ZMod p)) ≅ twoCoefficientLayers (ZMod p)) :=
    ⟨fun ⟨f⟩ => ⟨f ≪≫ onLatticeHomologySumIso Γ e⟩,
      fun ⟨f⟩ => ⟨f ≪≫ (onLatticeHomologySumIso Γ e).symm⟩⟩
  rw [he]
  unfold TwoLayer.onLatticeProfile TwoLayer.latticeRestriction
  rw [latticeMap_eq_coordinateEmbedding]


/-- All finite-index subgroups are tested by their actual mod-p image. -/
theorem decouplesOn_iff_isotropic :
    TwoLayer.DecouplesOn Γ e (checks (ZMod p)) ↔
      Isotropic (![-1, 0, 0] : Fin 3 → ZMod p) (image p 3 Γ) := by
  rw [decouplesOn_iff_couplingRestriction, couplingRestriction_iff_form,
    comp_reducedMap_zero_iff]
  constructor
  · intro h u hu v hv
    exact h ![u, v] (by intro i; fin_cases i <;> assumption)
  · intro h v hv
    have he : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
    rw [he, form_pair]
    exact h _ (hv 0) _ (hv 1)

/-- Every optimal index-p lattice, with no axis-alignment assumption. -/
theorem optimalLattice_iff (hind : Γ.index = p) :
    TwoLayer.DecouplesOn Γ e (checks (ZMod p)) ↔
      GluedMinimum.vertical ∈ image p 3 Γ := by
  rw [decouplesOn_iff_isotropic]
  exact GluedMinimum.indexPrime_isotropic_iff (-1 : ZMod p) (neg_ne_zero.mpr one_ne_zero) Γ hind

/-- Complete parametrization of the optimal actual subgroups: precisely
inverse images of planes containing the third coordinate direction. -/
theorem optimalLattices_complete :
    (Γ.index = p ∧ TwoLayer.DecouplesOn Γ e (checks (ZMod p))) ↔
      ∃ W : Submodule (ZMod p) (Residue p 3), Module.finrank (ZMod p) W = 2 ∧
        GluedMinimum.vertical ∈ W ∧ Γ = preimage p 3 W := by
  constructor
  · rintro ⟨hind, hd⟩
    refine ⟨image p 3 Γ, ?_, (optimalLattice_iff Γ e hind).mp hd,
      GluedMinimum.eq_preimage_of_index_prime Γ hind⟩
    have he := codim_add_finrank p 3 (image p 3 Γ)
    rw [GluedMinimum.codim_image_of_index_prime Γ hind] at he
    change Module.finrank (ZMod p) (image p 3 Γ) = 2
    omega
  · rintro ⟨W, hdim, hvert, hΓ⟩
    have hc : codim p 3 W = 1 := by
      have he := codim_add_finrank p 3 W
      change codim p 3 W + Module.finrank (ZMod p) W = 3 at he
      omega
    have hind : Γ.index = p := by rw [hΓ, preimage_index, hc, pow_one]
    exact ⟨hind, (optimalLattice_iff Γ e hind).mpr (by rwa [hΓ, image_preimage])⟩

/-- A choice-independent set of actual physically decoupling indices. -/
def physicalDecouplingIndices : Set ℕ :=
  {n | ∃ (Γ : AddSubgroup (Translation 3)) (hΓ : Γ.FiniteIndex),
    letI := hΓ
    ∃ e : Γ ≃+ Translation 3, TwoLayer.DecouplesOn Γ e (checks (ZMod p)) ∧ Γ.index = n}

/-- The actual displayed code has optimal coarse-cell index exactly p. -/
theorem physicalMinimum : IsLeast (physicalDecouplingIndices (p := p)) p := by
  have he : physicalDecouplingIndices (p := p) =
      {n : ℕ | ∃ Γ : AddSubgroup (Translation 3), Γ.FiniteIndex ∧
        Isotropic (![-1, 0, 0] : Fin 3 → ZMod p) (image p 3 Γ) ∧ Γ.index = n} := by
    ext n
    constructor
    · rintro ⟨Γ, hΓ, e, hd, hi⟩
      let := hΓ
      exact ⟨Γ, hΓ, (decouplesOn_iff_isotropic Γ e).mp hd, hi⟩
    · rintro ⟨Γ, hΓ, hd, hi⟩
      let := hΓ
      let e := LatticeBasis.coordinates Γ
      exact ⟨Γ, hΓ, e, (decouplesOn_iff_isotropic Γ e).mpr hd, hi⟩
  rw [he]
  exact minimumIndex_single_coefficient (-1 : ZMod p) (neg_ne_zero.mpr one_ne_zero)

end
end Decoupling.HighDim.Glued
