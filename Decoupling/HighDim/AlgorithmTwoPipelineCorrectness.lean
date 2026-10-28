import Decoupling.HighDim.AlgorithmTwoPipelinePhysical
import Decoupling.HighDim.AlgorithmTwoOriginalArraysSize

/-!
# Original-input correctness of the actual Algorithm 2 output

These are semantic endpoints for the same stored-stage execution, not new
runtime wrappers. Original formal profile data discharge all intermediate
basis, exactness, comparison and scalar-solvability conditions internally.
The physical gate word is exactly nonzeroProgram.value.gates. Its reported
ancillary numbers count the real plus/zero summands already used in the
stabilizer transport theorem, while identity-valued checks remain separate.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipeline
open CategoryTheory HomologicalComplex Matrix ArithmeticCost AlgorithmTwoFiniteComplex
open StableFree.Effective StableFree.Effective.CochainProgram
open AlgorithmTwoPhysicalTransport PhysicalIsomorphism
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
noncomputable section
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
variable (inp : Input (D := D) (L := L) (h := h) cC) (hDL : D ≤ L)

theorem finishProgram_multiplicities (q : Stages cC inp hDL) (j : Fin (D-1)) :
    (finishProgram cC inp hDL q).value.multiplicities.get j =
      Module.finrank K (Layers.coefficients (C.homology (j.val+1))) := by
  obtain ⟨old,⟨e⟩⟩ := inp.formal
  let basis := AlgorithmTwoComputedLayers.outputBasis cC old e
    (incoming cC inp hDL) (outgoing cC inp hDL)
    (incoming_action cC inp hDL) (outgoing_action cC inp hDL) j
  change q.layers.multiplicities.get j = _
  rw [q.layers.multiplicities_correct]
  exact ((Module.finrank_eq_card_basis basis).trans (Fintype.card_fin _)).symm

theorem nonzeroProgram_multiplicities (j : Fin (D-1)) :
    (nonzeroProgram cC inp hDL).value.multiplicities.get j =
      Module.finrank K (Layers.coefficients (C.homology (j.val+1))) :=
  finishProgram_multiplicities cC inp hDL (stagesProgram cC inp hDL).value j

/-- Identity-check metadata is exactly the free check ranks constructed
by C4, and does not itself represent a separate count of physical qudits. -/
theorem finishProgram_identityChecks (q : Stages cC inp hDL) :
    (finishProgram cC inp hDL q).value.sourceIdentityChecks =
      stableExtraC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction ∧
    (finishProgram cC inp hDL q).value.targetIdentityChecks =
      stableExtraT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction := ⟨rfl,rfl⟩

/-- Every reported ancillary count is the cardinality of the actual
identity-X or identity-Z coordinate block in the transport conclusion. -/
theorem finishProgram_ancilla_ranks (q : Stages cC inp hDL) :
    let ec := stableExtraC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let et := stableExtraT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let c1 := cC.rank 1+ec
    let t0 := targetRank cC inp hDL q.layers 0
    let t1 := targetRank cC inp hDL q.layers 1+et
    let o := (finishProgram cC inp hDL q).value
    o.sourceQ = cC.rank 0 ∧ o.targetQ = t0 ∧
    o.sourcePlus = sourcePlusCount t1 ∧ o.sourceZero = sourceZeroCount t0 c1 ∧
    o.targetPlus = targetPlusCount c1 ∧ o.targetZero = targetZeroCount (cC.rank 0) t1 ∧
    o.sourceAncillas = sourceAncillaCount c1 t0 t1 ∧
    o.targetAncillas = targetAncillaCount (cC.rank 0) c1 t1 := by
  simp only [sourcePlusCount,sourceZeroCount,targetPlusCount,targetZeroCount,
    sourceAncillaCount,targetAncillaCount,Fintype.card_fin,Fintype.card_sum]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem nonzeroProgram_ancilla_ranks :
    let q := (stagesProgram cC inp hDL).value
    let ec := stableExtraC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let et := stableExtraT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let c1 := cC.rank 1+ec
    let t0 := targetRank cC inp hDL q.layers 0
    let t1 := targetRank cC inp hDL q.layers 1+et
    let o := (nonzeroProgram cC inp hDL).value
    o.sourceQ = cC.rank 0 ∧ o.targetQ = t0 ∧
    o.sourcePlus = sourcePlusCount t1 ∧ o.sourceZero = sourceZeroCount t0 c1 ∧
    o.targetPlus = targetPlusCount c1 ∧ o.targetZero = targetZeroCount (cC.rank 0) t1 ∧
    o.sourceAncillas = sourceAncillaCount c1 t0 t1 ∧
    o.targetAncillas = targetAncillaCount (cC.rank 0) c1 t1 :=
  finishProgram_ancilla_ranks cC inp hDL (stagesProgram cC inp hDL).value

/-- Original adjacent arrays alone supply the pipeline input. No intermediate
comparison datum, exactness certificate, lift or gate word is an input. -/
theorem originalInput_transports
    (original : AlgorithmTwoOriginalArrays.Input (D := D) (L := L) (h := h) cC) :
    let inp := original.toPipeline cC
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
  nonzeroProgram_transports cC (original.toPipeline cC) hDL

theorem originalInput_multiplicities
    (original : AlgorithmTwoOriginalArrays.Input (D := D) (L := L) (h := h) cC) (j : Fin (D-1)) :
    (nonzeroProgram cC (original.toPipeline cC) hDL).value.multiplicities.get j =
      Module.finrank K (Layers.coefficients (C.homology (j.val+1))) :=
  nonzeroProgram_multiplicities cC (original.toPipeline cC) hDL j

end
end Decoupling.HighDim.AlgorithmTwoPipeline
