import Decoupling.HighDim.SequentialPipelineChecks

/- HD016: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of Algorithm 2”.
New sequential-contraction execution; historical AlgorithmTwoPipelinePhysical is preserved. -/
/-! # Both native stabilizer modules transported by the actual returned word -/
namespace Decoupling.HighDim.SequentialPipeline
open AlgorithmTwoPipeline
open CategoryTheory HomologicalComplex Matrix ArithmeticCost AlgorithmTwoFiniteComplex
open StableFree.Effective StableFree.Effective.CochainProgram
open AlgorithmTwoPhysicalTransport PhysicalIsomorphism
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
variable (inp : Input (D := D) (L := L) (h := h) cC) (hDL : D ≤ L)

/-- This statement uses the very gate list in the runtime output. The source
and target checks are the original degree windows with precisely the returned
identity-check rows and the actual plus/zero ancillary blocks. -/
theorem finishProgram_transports (q : Stages cC inp hDL) :
    let cT := originalFromFrame (AlgorithmTwoToricData.totalCoordinates D q.layers.multiplicities K)
    let ec := stableExtraC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let et := stableExtraT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    Transports (finishProgram cC inp hDL q).value.gates
      (ordinalIdentification (cC.rank 0) (cC.rank 1+ec) (cT.rank 0) (cT.rank 1+et))
      (sourceHX (identityChecksOrdinal (degreeMatrix cC 0 1) ec))
      (targetHX (identityChecksOrdinal (degreeMatrix cT 0 1) et))
      (sourceZ (degreeMatrix cC (-1) 0)) (targetZ (degreeMatrix cT (-1) 0)) ∧
    LocalCircuit (finishProgram cC inp hDL q).value.gates := by
  let : C.IsGE 1 := input_isGE cC inp
  let : (AlgorithmTwoToricData.nativeStack D q.layers.multiplicities K).IsGE 1 :=
    AlgorithmTwoToricData.nativeStack_isGE_one D q.layers.multiplicities K
  have hC (v) : LaurentArithmetic.matrixDenote q.stable.arrays.dC *ᵥ v = 0 ↔
      inImage (degreeMatrix cC (-1) 0) v := by
    rw [stable_original_dC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction q.stable]
    exact (identityChecksOrdinal_kernel _ _ v).trans (degreeMatrix_exact_zero cC v)
  have hT (v) : LaurentArithmetic.matrixDenote q.stable.arrays.dT *ᵥ v = 0 ↔
      inImage (degreeMatrix (originalFromFrame (AlgorithmTwoToricData.totalCoordinates D q.layers.multiplicities K)) (-1) 0) v := by
    rw [stable_original_dT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction q.stable]
    exact (identityChecksOrdinal_kernel
      (degreeMatrix (originalFromFrame (AlgorithmTwoToricData.totalCoordinates D q.layers.multiplicities K)) 0 1)
      (stableExtraT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction) v).trans
      (degreeMatrix_exact_zero (originalFromFrame (AlgorithmTwoToricData.totalCoordinates D q.layers.multiplicities K)) v)
  have ht := computed_transports q.stable.arrays.dC q.stable.arrays.dT q.stable.arrays.forward q.stable.arrays.inverse
    (storedStable_solvable cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction q.stable)
    (degreeMatrix cC (-1) 0)
    (degreeMatrix (originalFromFrame (AlgorithmTwoToricData.totalCoordinates D q.layers.multiplicities K)) (-1) 0) hC hT
  rw [stable_original_dC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction q.stable,
    stable_original_dT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction q.stable] at ht
  exact ht

/-- The final pipeline preserves the physical conclusion without a new choice
of matrices, maps or gates. -/
theorem nonzeroProgram_transports :
    let q := (stagesProgram cC inp hDL).value
    let cT := originalFromFrame (AlgorithmTwoToricData.totalCoordinates D q.layers.multiplicities K)
    let ec := stableExtraC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let et := stableExtraT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    Transports (nonzeroProgram cC inp hDL).value.gates
      (ordinalIdentification (cC.rank 0) (cC.rank 1+ec) (cT.rank 0) (cT.rank 1+et))
      (sourceHX (identityChecksOrdinal (degreeMatrix cC 0 1) ec))
      (targetHX (identityChecksOrdinal (degreeMatrix cT 0 1) et))
      (sourceZ (degreeMatrix cC (-1) 0)) (targetZ (degreeMatrix cT (-1) 0)) ∧
    LocalCircuit (nonzeroProgram cC inp hDL).value.gates :=
  finishProgram_transports cC inp hDL (stagesProgram cC inp hDL).value

theorem nonzeroProgram_nativeEquivalence :
    Nonempty (HomotopyEquiv
      (AlgorithmTwoToricData.nativeStack D (nonzeroProgram cC inp hDL).value.multiplicities K) C) := by
  let q := (stagesProgram cC inp hDL).value
  exact ⟨computedEquivalence cC inp hDL q.layers q.target q.gamma q.homotopy⟩

theorem nonzeroProgram_species :
    let o := (nonzeroProgram cC inp hDL).value
    o.sourceQ+o.sourceAncillas=o.species ∧ o.targetQ+o.targetAncillas=o.species :=
  finishProgram_species cC inp hDL (stagesProgram cC inp hDL).value

end
end Decoupling.HighDim.SequentialPipeline
