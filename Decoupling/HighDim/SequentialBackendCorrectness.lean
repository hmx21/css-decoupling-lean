import Decoupling.HighDim.AlgorithmTwoBackendCorrectness
import Decoupling.HighDim.SequentialPipelineMaterialized
import Decoupling.HighDim.SequentialPipelineCorrectness

/- HD016: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of Algorithm 2”.
New sequential-contraction execution; historical AlgorithmTwoBackendCorrectness is preserved. -/
/-!
# Correctness of the finite-array execution entry

The actual pure backend has only finite rank/coefficient data and the original
complex/profile promise in Prop as inputs. Whole-Work equality with the proved
program transfers its native toric target, multiplicities, locality and rank
metadata. Both the literal empty branch and the complete nonzero branch are
included. No native coordinate object is an executable argument.
-/
namespace Decoupling.HighDim.SequentialBackend
open AlgorithmTwoPipeline AlgorithmTwoPipelineBackend AlgorithmTwo
open SequentialPipeline
open CategoryTheory CategoryTheory.Limits HomologicalComplex ArithmeticCost
open AlgorithmTwoPipeline PhysicalIsomorphism
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
attribute [local instance] HasDerivedCategory.standard
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}

noncomputable section
variable (raw : RawInput K D L h) (valid : Valid raw) (hDL : D ≤ L)

theorem execute_zero (hz : storedRank raw = 0) :
    execute raw valid hDL = AlgorithmTwo.emptyProgram K D := by
  rw [execute_eq_program]
  apply SequentialAlgorithmTwo.program_zero
  rw [coordinates_inputRank, hz]

theorem execute_nonzero (hz : storedRank raw ≠ 0) :
    execute raw valid hDL =
      SequentialPipeline.nonzeroProgram (modelCoordinates raw valid)
        ((modelInput raw valid).toPipeline (modelCoordinates raw valid)) hDL := by
  rw [execute_eq_program]
  apply SequentialAlgorithmTwo.program_nonzero
  rwa [coordinates_inputRank]

omit [DecidableEq K] in
private theorem nativeStack_empty :
    AlgorithmTwoToricData.nativeStack D (RuntimeOutput.empty K D).multiplicities K =
      emptyTarget K D := by
  have ht : AlgorithmTwoToricData.multiplicities D
      (RuntimeOutput.empty K D).multiplicities = fun _ => 0 := by
    funext j
    simp [AlgorithmTwoToricData.multiplicities,RuntimeOutput.empty]
  unfold AlgorithmTwoToricData.nativeStack
  rw [ht]
  rfl

/-- The native target is rebuilt from exactly the returned multiplicity vector. -/
theorem execute_nativeEquivalence :
    Nonempty (HomotopyEquiv
      (AlgorithmTwoToricData.nativeStack D (execute raw valid hDL).value.multiplicities K)
      (model raw valid)) := by
  by_cases hz : storedRank raw = 0
  · rw [execute_zero raw valid hDL hz]
    change Nonempty (HomotopyEquiv
      (AlgorithmTwoToricData.nativeStack D (RuntimeOutput.empty K D).multiplicities K) _)
    rw [nativeStack_empty]
    exact ⟨(emptyEquivalence (modelCoordinates raw valid)
      ((coordinates_inputRank raw (Classical.choose valid)).trans hz)).symm⟩
  · rw [execute_nonzero raw valid hDL hz]
    exact SequentialPipeline.nonzeroProgram_nativeEquivalence (modelCoordinates raw valid)
      ((modelInput raw valid).toPipeline (modelCoordinates raw valid)) hDL

theorem execute_multiplicities (j : Fin (D-1)) :
    (execute raw valid hDL).value.multiplicities.get j =
      Module.finrank K (Layers.coefficients ((model raw valid).homology (j.val+1))) := by
  by_cases hz : storedRank raw = 0
  · rw [execute_zero raw valid hDL hz]
    have hC : IsZero (model raw valid) :=
      complex_isZero_of_total_zero (modelCoordinates raw valid)
        ((coordinates_inputRank raw (Classical.choose valid)).trans hz)
    have hH : IsZero ((model raw valid).homology (j.val+1)) :=
      (homologyFunctor (ModuleCat (Laurent K D)) (ComplexShape.up ℤ) (j.val+1)).map_isZero hC
    let : Subsingleton (Layers.coefficients ((model raw valid).homology (j.val+1))) := by
      change Subsingleton ((model raw valid).homology (j.val+1))
      exact ModuleCat.subsingleton_of_isZero hH
    change (Vector.replicate (D-1) 0)[j.val] = _
    rw [Vector.getElem_replicate]
    exact (Module.finrank_zero_of_subsingleton
      (R := K) (M := Layers.coefficients ((model raw valid).homology (j.val+1)))).symm
  · rw [execute_nonzero raw valid hDL hz]
    exact SequentialPipeline.nonzeroProgram_multiplicities (modelCoordinates raw valid)
      ((modelInput raw valid).toPipeline (modelCoordinates raw valid)) hDL j

theorem execute_local : LocalCircuit (execute raw valid hDL).value.gates :=
  localCircuit _

theorem execute_species :
    let o := (execute raw valid hDL).value
    o.sourceQ + o.sourceAncillas = o.species ∧
      o.targetQ + o.targetAncillas = o.species := by
  by_cases hz : storedRank raw = 0
  · rw [execute_zero raw valid hDL hz]
    exact ⟨rfl,rfl⟩
  · rw [execute_nonzero raw valid hDL hz]
    exact SequentialPipeline.nonzeroProgram_species (modelCoordinates raw valid)
      ((modelInput raw valid).toPipeline (modelCoordinates raw valid)) hDL

/-- The reported original qudit count is the literal degree-zero input rank. -/
theorem execute_sourceQ :
    (execute raw valid hDL).value.sourceQ = rankAt raw.ranks 0 := by
  by_cases hz : storedRank raw = 0
  · rw [execute_zero raw valid hDL hz,storedRank_zero_rank raw valid hz 0]
    rfl
  · rw [execute_nonzero raw valid hDL hz]
    rfl

variable (a : MaterializedInput K D L h) (ha : Valid a.toRaw)

theorem executeMaterialized_nativeEquivalence :
    Nonempty (HomotopyEquiv
      (AlgorithmTwoToricData.nativeStack D
        (executeMaterialized a ha hDL).value.multiplicities K)
      (model a.toRaw ha)) :=
  execute_nativeEquivalence a.toRaw ha hDL

theorem executeMaterialized_multiplicities (j : Fin (D-1)) :
    (executeMaterialized a ha hDL).value.multiplicities.get j =
      Module.finrank K (Layers.coefficients ((model a.toRaw ha).homology (j.val+1))) :=
  execute_multiplicities a.toRaw ha hDL j

theorem executeMaterialized_local :
    LocalCircuit (executeMaterialized a ha hDL).value.gates :=
  execute_local a.toRaw ha hDL

theorem executeMaterialized_species :
    let o := (executeMaterialized a ha hDL).value
    o.sourceQ + o.sourceAncillas = o.species ∧
      o.targetQ + o.targetAncillas = o.species :=
  execute_species a.toRaw ha hDL

theorem executeMaterialized_sourceQ :
    (executeMaterialized a ha hDL).value.sourceQ = rankAt a.ranks 0 :=
  execute_sourceQ a.toRaw ha hDL

end
end Decoupling.HighDim.SequentialBackend
