import Decoupling.HighDim.TorusTensorMaps
import Decoupling.HighDim.TorusPeriodicBridge

/-!
# HD010 Lemmas 10 and 11 in actual tensor-model form

The profile model is constructed from the literal CSS checks. Arbitrary
layer model independence follows from the genuine natural comparison;
canonical layer model existence is packaged in the subsequent interface.
-/
namespace Decoupling.HighDim.Torus
open CategoryTheory CategoryTheory.Limits FiniteResolution ScalingLattice
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] {D q s r : ℕ}

def cssTensorModel (c : CSS.Checks K D q s r) (hc : c.Topological) :
    TensorModel (Profile.S_X c) where
  complex := cssComplex c hc
  lower := -(D + 2 : ℕ)
  upper := D + 2
  finite := fun _ => inferInstance
  free := fun _ => inferInstance
  boundedBelow := inferInstance
  boundedAbove := inferInstance
  iso := cssComplex_profileIso c hc

/-- An actual model of the profile on an arbitrary finite-index period
lattice, built from its actual physical coarse checks. -/
def periodicProfileModel (L : AddSubgroup (Translation D)) [L.FiniteIndex]
    (e : L ≃+ Translation D) (c : CSS.Checks K D q s r) (hc : c.Topological) :
    TensorModel ((ModuleCat.restrictScalars (coordinateEmbedding K L e)).mapDerivedCategory.obj
      (Profile.S_X c)) :=
  { cssTensorModel (physicalChecks K L e c) (physicalChecks_topological K L e c hc) with
    iso := cssComplex_profileIso _ _ ≪≫ (physicalChecksRestrictionIso K L e c).symm }

/-- Lemma 10 as a coefficient-linear equivalence, stronger than the
dimension equality: the source is the literal periodic logical quotient. -/
def logicalTensorModelEquiv (L : AddSubgroup (Translation D)) [L.FiniteIndex]
    (e : L ≃+ Translation D) (c : CSS.Checks K D q s r) (hc : c.Topological) :
    Logical L c hc ≃ₗ[K] (periodicProfileModel L e c hc).H0 :=
  (logicalProfileEquiv L e c hc).trans
    (((homCoefficientsIso (probe K D) (physicalChecksRestrictionIso K L e c).symm).toLinearEquiv).trans
      (periodicProfileModel L e c hc).equiv.symm)

theorem logicalQudits_eq_periodicTensor (L : AddSubgroup (Translation D)) [L.FiniteIndex]
    (e : L ≃+ Translation D) (c : CSS.Checks K D q s r) (hc : c.Topological) :
    logicalQudits L c hc = Module.finrank K (periodicProfileModel L e c hc).H0 :=
  (logicalTensorModelEquiv L e c hc).finrank_eq

/-- Lemma 11's bound holds for every actual bounded finite-free model
of the shifted layer, with no trivial-action assumption. -/
theorem tensor_layer_finrank_le (E : ModuleCat (Laurent K D)) [Module.Finite K (Layers.coefficients E)]
    (j : ℕ) (hj : j < D)
    (M : TensorModel ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj E)) :
    Module.finrank K M.H0 ≤ D.choose j * Module.finrank K (Layers.coefficients E) := by
  rw [M.equiv.finrank_eq]
  exact probeSingle_finrank_le E j hj

/-- Lemma 11's equality characterization for actual tensor homology,
including all interior degrees and arbitrary translation actions. -/
theorem tensor_layer_finrank_eq_iff (E : ModuleCat (Laurent K D)) [Module.Finite K (Layers.coefficients E)]
    (j : ℕ) (hj : 1 ≤ j) (hjD : j < D)
    (M : TensorModel ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj E)) :
    Module.finrank K M.H0 = D.choose j * Module.finrank K (Layers.coefficients E) ↔
      TrivialLayers.AugmentationAction E := by
  rw [M.equiv.finrank_eq]
  exact probeSingle_finrank_eq_iff E j hj hjD

end
end Decoupling.HighDim.Torus
