import Decoupling.HighDim.AlgorithmOneFiniteInputArrays
import Decoupling.HighDim.AlgorithmTwoOriginalMaterializedCorrectness

/-!
# No additional mathematical input hypothesis at the Algorithm 1/2 boundary

The original topological and finite-layer hypotheses provide a valid
finite-vector input representing the actual successfully restricted complex.
The conclusion includes a genuine cochain isomorphism to that complex,
so an unrelated empty input cannot satisfy the construction.

This is mathematical input existence. It neither chooses a physical
degree-zero basis during execution nor asserts an effective or polynomial
Algorithm 1 implementation.
-/
namespace Decoupling.HighDim.AlgorithmOne
open CategoryTheory AlgorithmTwoPipelineBackend AlgorithmTwoBackendOriginal
variable {p D q s r : ℕ} [Fact p.Prime]
  (c : CSS.Checks (ZMod p) D q s r)

theorem successComplex_materializedInput_exists
    (hc : c.Topological) (hD : 2 ≤ D) (h : Layers.FiniteXLayers c) :
    ∃ B : ℕ, ∃ a : MaterializedInput (ZMod p) D (D+2) B,
      ∃ valid : Valid a.toRaw,
        Nonempty (successComplex c hc h ≅ model a.toRaw valid) := by
  obtain ⟨coords,B,⟨inp⟩⟩ := successComplex_originalInput_exists c hc hD h
  exact ⟨B,materializedInput coords inp,materialized_valid coords inp,
    ⟨materializedNativeIso coords inp⟩⟩

end Decoupling.HighDim.AlgorithmOne
