import Decoupling.HighDim.TorusPeriodicBridge
import Decoupling.HighDim.TorusProfileEquality
import Decoupling.HighDim.TwoLayerLattice

/-!
# Corollary 3: unconditional finite-torus counting bound

The period lattice is arbitrary of finite index. The dimension is that
of the actual periodic check quotient, and the right side uses the
original native Ext multiplicities. Maximal count is proved to force
containment in the common translation kernel; this is a conclusion.
The remaining equality/formality direction is developed separately.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits ScalingLattice
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {p D q s r : ℕ} [Fact p.Prime]
  (L : AddSubgroup (Translation D)) [L.FiniteIndex] (e : L ≃+ Translation D)
  (c : CSS.Checks (ZMod p) D q s r)

/-- Coarse-graining preserves the original coefficient-field vector
space of each actual positive native Ext layer. -/
def physicalLayerCoefficientEquiv (n : ℕ) :
    Layers.coefficients (Layers.layer (physicalChecks (ZMod p) L e c) (n + 1)) ≃ₗ[ZMod p]
      Layers.coefficients (Layers.layer c (n + 1)) :=
  ((ModuleCat.restrictScalars (constant : ZMod p →+* Laurent (ZMod p) D)).mapIso
    (TwoLayer.physicalLayerIso L e c n)).toLinearEquiv.trans
      (TrivialLayers.coefficientRestrictionEquiv L e (Layers.layer c (n + 1)))

theorem physicalMultiplicity_eq (j : ℕ) (hj : 1 ≤ j) :
    Layers.multiplicity (physicalChecks (ZMod p) L e c) j = Layers.multiplicity c j := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact (physicalLayerCoefficientEquiv L e c n).finrank_eq

theorem physicalFiniteLayers (h : Layers.FiniteXLayers c) :
    Layers.FiniteXLayers (physicalChecks (ZMod p) L e c) := by
  intro j hj hjD
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  let := h (n + 1) hj hjD
  exact Module.Finite.equiv (physicalLayerCoefficientEquiv L e c n).symm

theorem physicalLayerBound_eq : layerBound (physicalChecks (ZMod p) L e c) = layerBound c := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [physicalMultiplicity_eq L e c j (Finset.mem_Ico.mp hj).1]

include e in
/-- Corollary 3, inequality, on every finite-index period lattice. -/
theorem logicalQudits_le (hc : c.Topological) (hD : 1 ≤ D) (h : Layers.FiniteXLayers c) :
    logicalQudits L c hc ≤ layerBound c := by
  rw [logicalQudits_eq_profile L e c hc, ← physicalLayerBound_eq L e c]
  exact (profile_finrank_le (physicalChecks (ZMod p) L e c)
    (physicalChecks_topological (ZMod p) L e c hc) hD (physicalFiniteLayers L e c h)).2

include e in
/-- Equality forces triviality of every original layer on precisely the
given period lattice. No normalization lattice is assumed beforehand. -/
theorem maximalCount_le_commonKernel (hc : c.Topological) (hD : 1 ≤ D)
    (h : Layers.FiniteXLayers c) (heq : logicalQudits L c hc = layerBound c) :
    L ≤ Translations.lambda0 c := by
  rw [logicalQudits_eq_profile L e c hc, ← physicalLayerBound_eq L e c] at heq
  apply (TwoLayer.le_lambda0_iff_restricted_layers_augmentation L e c).mpr
  intro j hj hjD
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  exact ScalingSplitting.augmentationAction_of_iso (TwoLayer.physicalLayerIso L e c n)
    (profile_equality_implies_augmentation (physicalChecks (ZMod p) L e c)
      (physicalChecks_topological (ZMod p) L e c hc) hD (physicalFiniteLayers L e c h)
        heq (n + 1) hj hjD)

end
end Decoupling.HighDim.Torus
