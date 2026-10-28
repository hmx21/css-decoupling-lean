import Decoupling.HighDim.SchreyerAlgorithmOne
import Decoupling.HighDim.AlgorithmOneFiniteInputArrays
import Decoupling.HighDim.AlgorithmTwoOriginalMaterializedCorrectness

/-!
# HD014 new Schreyer success model supplies the actual Algorithm 2 input

The original topology, D ≥ 2 and finite X layers suffice for finite-power
coordinates, genuine adjacent dense arrays, and a valid stored-vector input.
The conclusion contains a cochain isomorphism from the actual restriction
of the new Schreyer model, so an unrelated empty input cannot witness it.
Only generic finite-free input and materialization results are reused;
no legacy CSS success complex is inserted.

This is mathematical input existence. No executable basis selection,
physical interpretation of arbitrary degree-zero coordinates, or runtime
bound for Algorithm 1/input preparation is asserted.
-/
namespace Decoupling.HighDim.SchreyerAlgorithmOne
open CategoryTheory AlgorithmTwoPipelineBackend AlgorithmTwoBackendOriginal
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {p D q s r : ℕ} [Fact p.Prime] (c : CSS.Checks (ZMod p) D q s r)

/-- Every chosen coordinate system on the actual new restricted model has
an honest finite common-box representation of its adjacent differentials. -/
theorem successComplex_originalInput_of_coordinates
    (hc : c.Topological) (hD : 2 ≤ D) (h : Layers.FiniteXLayers c)
    (coords : StableFree.Coordinates (successComplex c hc h)) :
    ∃ B : ℕ, Nonempty (AlgorithmTwoOriginalArrays.Input (D := D) (L := D+2) (h := B) coords) := by
  let : (successComplex c hc h).IsStrictlyLE ((D+2 : ℕ) : ℤ) :=
    successComplex_strictlyLE c hc h (by omega)
  exact AlgorithmOne.originalInput_exists coords (successComplex_formal c hc hD h)

/-- No finite-free coordinates or differential arrays remain an input hypothesis. -/
theorem successComplex_originalInput_exists
    (hc : c.Topological) (hD : 2 ≤ D) (h : Layers.FiniteXLayers c) :
    ∃ coords : StableFree.Coordinates (successComplex c hc h),
      ∃ B : ℕ, Nonempty (AlgorithmTwoOriginalArrays.Input (D := D) (L := D+2) (h := B) coords) := by
  obtain ⟨coords⟩ := successComplex_coordinates c hc h
  exact ⟨coords,successComplex_originalInput_of_coordinates c hc hD h coords⟩

/-- The stored finite-vector input represents this actual new success complex. -/
theorem successComplex_materializedInput_exists
    (hc : c.Topological) (hD : 2 ≤ D) (h : Layers.FiniteXLayers c) :
    ∃ B : ℕ, ∃ a : MaterializedInput (ZMod p) D (D+2) B,
      ∃ valid : Valid a.toRaw,
        Nonempty (successComplex c hc h ≅ AlgorithmTwoPipelineBackend.model a.toRaw valid) := by
  let : (successComplex c hc h).IsStrictlyLE ((D+2 : ℕ) : ℤ) :=
    successComplex_strictlyLE c hc h (by omega)
  obtain ⟨coords,B,⟨inp⟩⟩ := successComplex_originalInput_exists c hc hD h
  exact ⟨B,materializedInput coords inp,materialized_valid coords inp,
    ⟨materializedNativeIso coords inp⟩⟩

/-- The existing actual public program returns a target homotopy equivalent
to the new restricted Schreyer model, for the same stored coefficient input. -/
theorem successComplex_materializedExecution_exists
    (hc : c.Topological) (hD : 2 ≤ D) (h : Layers.FiniteXLayers c) :
    ∃ B : ℕ, ∃ a : MaterializedInput (ZMod p) D (D+2) B,
      ∃ valid : Valid a.toRaw,
        Nonempty (successComplex c hc h ≅ AlgorithmTwoPipelineBackend.model a.toRaw valid) ∧
        Nonempty (HomotopyEquiv
          (AlgorithmTwoToricData.nativeStack D
            (executeMaterialized a valid (by omega : D ≤ D+2)).value.multiplicities (ZMod p))
          (successComplex c hc h)) := by
  obtain ⟨B,a,valid,⟨e⟩⟩ := successComplex_materializedInput_exists c hc hD h
  obtain ⟨hE⟩ := executeMaterialized_nativeEquivalence (by omega : D ≤ D+2) a valid
  exact ⟨B,a,valid,⟨e⟩,⟨hE.trans (HomotopyEquiv.ofIso e.symm)⟩⟩

end
end Decoupling.HighDim.SchreyerAlgorithmOne
