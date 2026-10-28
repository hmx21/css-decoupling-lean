import Decoupling.HighDim.TorusExactLoss
import Decoupling.HighDim.TorusTensorMapsShift
import Decoupling.HighDim.PerfectModelAdjacent
import Decoupling.HighDim.TorusCountBound
import Decoupling.HighDim.TwoLayerCriterion

/-!
# HD010 equation B1 with all model-existence inputs discharged

The models are constructed from the actual finite homology modules by
the proved resolution/cone induction. Inclusion and connecting maps
are actual lift-then-tensor homology maps of the canonical adjacent triangle.
-/
namespace Decoupling.HighDim.Torus
open CategoryTheory CategoryTheory.Limits PostnikovInduction
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] {D : ℕ}

section General
variable (s : Finset ℤ) (X : Derived.{0} K D) (hX : Supported X s)
  (hfin : ∀ i ∈ s, Module.Finite K (Layers.coefficients (H X i))) (j : ℤ)

abbrev lowerTorus := (PerfectModel.lowerModel s X hX hfin j).H0
abbrev capTorus := (PerfectModel.capModel s X hX hfin j).H0
abbrev layerTorus := (PerfectModel.layerModel s X hX hfin j).H0
abbrev lowerShiftTorus := (PerfectModel.shift (PerfectModel.lowerModel s X hX hfin j) 1).H0

def inclusionTorus : lowerTorus s X hX hfin j ⟶ capTorus s X hX hfin j :=
  TensorModel.map (PerfectModel.lowerModel s X hX hfin j)
    (PerfectModel.capModel s X hX hfin j) (AdjacentGluing.rawTriangle X j).mor₁

def connectingTorus : layerTorus s X hX hfin j ⟶ lowerShiftTorus s X hX hfin j :=
  TensorModel.map (PerfectModel.layerModel s X hX hfin j)
    (PerfectModel.shift (PerfectModel.lowerModel s X hX hfin j) 1) (AdjacentGluing.delta X j)

/-- The same actual connecting map with codomain literally H¹ of the
unshifted lower tensor complex, via the canonical shift identification. -/
def connectingTorusH1 : layerTorus s X hX hfin j ⟶
    tensorHi (PerfectModel.lowerModel s X hX hfin j).complex 1 :=
  connectingTorus s X hX hfin j ≫
    (TensorModel.shiftH0Iso (PerfectModel.lowerModel s X hX hfin j) 1).hom

theorem connectingTorusH1_rank :
    Module.finrank K (connectingTorusH1 s X hX hfin j).hom.range =
      Module.finrank K (connectingTorus s X hX hfin j).hom.range :=
  finrank_range_postcompose_iso _ _

/-- B1 in its subtraction-free natural-number form, with both exact losses. -/
theorem exact_loss :
    Module.finrank K (capTorus s X hX hfin j) +
      Module.finrank K (inclusionTorus s X hX hfin j).hom.ker +
      Module.finrank K (connectingTorus s X hX hfin j).hom.range =
        Module.finrank K (lowerTorus s X hX hfin j) +
          Module.finrank K (layerTorus s X hX hfin j) :=
  adjacent_tensor_dimension X j (PerfectModel.lowerModel s X hX hfin j)
    (PerfectModel.capModel s X hX hfin j) (PerfectModel.layerModel s X hX hfin j)
    (PerfectModel.shift (PerfectModel.lowerModel s X hX hfin j) 1)

/-- The literal subtraction form displayed as equation B1. -/
theorem exact_loss_subtraction :
    Module.finrank K (capTorus s X hX hfin j) =
      Module.finrank K (lowerTorus s X hX hfin j) +
        Module.finrank K (layerTorus s X hX hfin j) -
          Module.finrank K (inclusionTorus s X hX hfin j).hom.ker -
            Module.finrank K (connectingTorus s X hX hfin j).hom.range := by
  have h := exact_loss s X hX hfin j
  omega

/-- B1 with the image lying in actual H¹ of the lower tensor complex. -/
theorem exact_loss_H1 :
    Module.finrank K (capTorus s X hX hfin j) =
      Module.finrank K (lowerTorus s X hX hfin j) +
        Module.finrank K (layerTorus s X hX hfin j) -
          Module.finrank K (inclusionTorus s X hX hfin j).hom.ker -
            Module.finrank K (connectingTorusH1 s X hX hfin j).hom.range := by
  rw [connectingTorusH1_rank]
  exact exact_loss_subtraction s X hX hfin j

end General

variable {p q sx sz : ℕ} [Fact p.Prime]

theorem profile_support_finite_coefficients (c : CSS.Checks (ZMod p) D q sx sz)
    (h : Layers.FiniteXLayers c) (i : ℤ) (hi : i ∈ Profile.support c) :
    Module.Finite (ZMod p) (Layers.coefficients (H (Profile.S_X c) i)) := by
  obtain ⟨n, hn, hnD, _, rfl⟩ := (Profile.mem_support_iff c i).mp hi
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let := h (n + 1) (by omega) hnD
  let eh : H (Profile.S_X c) (n + 1 : ℕ) ≅ Layers.layer c (n + 1) :=
    (Profile.homologyEquivLayer c n).toModuleIso
  let ec : Layers.coefficients (H (Profile.S_X c) (n + 1 : ℕ)) ≅
      Layers.coefficients (Layers.layer c (n + 1)) :=
    (ModuleCat.restrictScalars (constant : ZMod p →+* Laurent (ZMod p) D)).mapIso eh
  exact Module.Finite.equiv ec.symm.toLinearEquiv

theorem restricted_support_finite_coefficients
    (L : AddSubgroup (Translation D)) [L.FiniteIndex] (e : L ≃+ Translation D)
    (c : CSS.Checks (ZMod p) D q sx sz) (h : Layers.FiniteXLayers c)
    (i : ℤ) (hi : i ∈ Profile.support c) :
    Module.Finite (ZMod p) (Layers.coefficients (H (TwoLayer.onLatticeProfile L e c) i)) := by
  let := profile_support_finite_coefficients c h i hi
  let ec := ((ModuleCat.restrictScalars (constant : ZMod p →+* Laurent (ZMod p) D)).mapIso
    (ExactDerivedHomology.homologyIso (TwoLayer.latticeRestriction L e) (Profile.S_X c) i)).toLinearEquiv
  exact Module.Finite.equiv (ec.trans
    (TrivialLayers.coefficientRestrictionEquiv L e (H (Profile.S_X c) i))).symm

/-- Equation B1 for the actual profile on an arbitrary period lattice.
No common-kernel inclusion, trivial action, splitting, or free-model
existence hypothesis is present. Every integer truncation degree is allowed. -/
theorem period_exact_loss
    (L : AddSubgroup (Translation D)) [L.FiniteIndex] (e : L ≃+ Translation D)
    (c : CSS.Checks (ZMod p) D q sx sz) (hc : c.Topological) (hD : 1 ≤ D)
    (h : Layers.FiniteXLayers c) (j : ℤ) :
    let X := TwoLayer.onLatticeProfile L e c
    let hX := TwoLayer.onLattice_supported L e c hc hD
    let hfin := restricted_support_finite_coefficients L e c h
    Module.finrank (ZMod p) (capTorus (Profile.support c) X hX hfin j) +
      Module.finrank (ZMod p) (inclusionTorus (Profile.support c) X hX hfin j).hom.ker +
      Module.finrank (ZMod p) (connectingTorus (Profile.support c) X hX hfin j).hom.range =
        Module.finrank (ZMod p) (lowerTorus (Profile.support c) X hX hfin j) +
          Module.finrank (ZMod p) (layerTorus (Profile.support c) X hX hfin j) :=
  exact_loss _ _ _ _ j

end
end Decoupling.HighDim.Torus
