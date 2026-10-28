import Decoupling.HighDim.TorusPaperLayers
import Decoupling.HighDim.TorusTensorMapsContractionCells
import Decoupling.HighDim.TorusExactLossPaper
import Decoupling.HighDim.TorusCorollary
import Decoupling.HighDim.DecouplingCriterionMultiplicity

/-!
# HD010 torus lemmas and Corollary 3

No model existence is assumed: the single-layer model is constructed
from the genuine finite-free Laurent resolution. The final physical
predicate existentially quantifies toric multiplicities as in Theorem 1.
-/
namespace Decoupling.HighDim.Torus
open CategoryTheory
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {D : ℕ}

def layerTensorModel (E : ModuleCat (Laurent K D)) [Module.Finite K (Layers.coefficients E)]
    (j : ℕ) : TensorModel ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj E) := by
  let := PerfectModel.finite_of_coefficients E
  exact Classical.choice (PerfectModel.single_exists E j)

/-- Lemma 11, directly on the H⁰ of the constructed derived tensor model. -/
theorem torus_layer (E : ModuleCat (Laurent K D)) [Module.Finite K (Layers.coefficients E)]
    (j : ℕ) (hj : 1 ≤ j) (hjD : j < D) :
    Module.finrank K (layerTensorModel E j).H0 ≤ D.choose j * Module.finrank K (Layers.coefficients E) ∧
      (Module.finrank K (layerTensorModel E j).H0 = D.choose j * Module.finrank K (Layers.coefficients E) ↔
        TrivialLayers.AugmentationAction E) :=
  ⟨tensor_layer_finrank_le E j hjD _, tensor_layer_finrank_eq_iff E j hj hjD _⟩

variable {p q sx sz : ℕ} [Fact p.Prime]

/-- The current manuscript's Corollary 3, with actual periodic logical
dimension and the existential-multiplicity physical predicate. -/
theorem paper_corollary3
    (L : AddSubgroup (Translation D)) [L.FiniteIndex]
    (c : CSS.Checks (ZMod p) D q sx sz) (hc : c.Topological) (hD : 2 ≤ D)
    (h : Layers.FiniteXLayers c) :
    logicalQudits L c hc ≤ layerBound c ∧
      (logicalQudits L c hc = layerBound c ↔
        DecouplingCriterion.DecouplesOn L (LatticeBasis.coordinates L) c) := by
  rw [DecouplingCriterion.decouples_iff_original_multiplicities L (LatticeBasis.coordinates L)
    c hc (by omega) h]
  exact corollary3 L c hc hD h

end
end Decoupling.HighDim.Torus
