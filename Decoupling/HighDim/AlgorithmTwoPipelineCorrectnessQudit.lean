import Decoupling.HighDim.AlgorithmTwoPipelineCorrectness

/-!
# Native p-ary physical conclusion for the actual pipeline output

This combines the exact two-stabilizer transport, the real local complex
unitaries and the normalized ancillary fixed spaces for the same computed
word. The ancillary indices are the literal summands of the stabilized
checks, and the reported counts are proved to be their cardinalities.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipeline
open CategoryTheory HomologicalComplex Matrix ArithmeticCost AlgorithmTwoFiniteComplex
open StableFree.Effective StableFree.Effective.CochainProgram
open AlgorithmTwoPhysicalTransport PhysicalIsomorphism
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
variable {p D L h : ℕ} [Fact p.Prime]
variable {C : CochainComplex (ModuleCat (Laurent (ZMod p) D)) ℤ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
variable (inp : Input (D := D) (L := L) (h := h) cC) (hDL : D ≤ L)

theorem nonzeroProgram_physical (Cells : Type*) [Fintype Cells] [DecidableEq Cells] :
    let q := (stagesProgram cC inp hDL).value
    let cT := originalFromFrame (AlgorithmTwoToricData.totalCoordinates D q.layers.multiplicities (ZMod p))
    let ec := stableExtraC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let et := stableExtraT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let c1 := cC.rank 1+ec
    let t0 := cT.rank 0
    let t1 := cT.rank 1+et
    let o := (nonzeroProgram cC inp hDL).value
    Transports o.gates (ordinalIdentification (cC.rank 0) c1 t0 t1)
      (sourceHX (identityChecksOrdinal (degreeMatrix cC 0 1) ec))
      (targetHX (identityChecksOrdinal (degreeMatrix cT 0 1) et))
      (sourceZ (degreeMatrix cC (-1) 0)) (targetZ (degreeMatrix cT (-1) 0)) ∧
    LocalCircuit o.gates ∧ LocalPauliSemantics o.gates ∧
    ProductAncillaSemantics p (Fin t1 × Cells) ((Fin t0 ⊕ Fin c1) × Cells) ∧
    ProductAncillaSemantics p (Fin c1 × Cells) ((Fin (cC.rank 0) ⊕ Fin t1) × Cells) ∧
    o.sourceAncillas = sourceAncillaCount c1 t0 t1 ∧
    o.targetAncillas = targetAncillaCount (cC.rank 0) c1 t1 := by
  have ht := nonzeroProgram_transports cC inp hDL
  have hm := nonzeroProgram_ancilla_ranks cC inp hDL
  refine ⟨ht.1,ht.2,localPauliSemantics _,productAncillaSemantics _ _ _,
    productAncillaSemantics _ _ _,?_,?_⟩
  · exact hm.2.2.2.2.2.2.1
  · exact hm.2.2.2.2.2.2.2

/-- The same physical endpoint from the original adjacent coefficient input;
no intermediate maps, comparisons, scalar certificates or gate words enter. -/
theorem originalInput_physical
    (original : AlgorithmTwoOriginalArrays.Input (D := D) (L := L) (h := h) cC)
    (Cells : Type*) [Fintype Cells] [DecidableEq Cells] :
    let inp := original.toPipeline cC
    let q := (stagesProgram cC inp hDL).value
    let cT := originalFromFrame (AlgorithmTwoToricData.totalCoordinates D q.layers.multiplicities (ZMod p))
    let ec := stableExtraC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let et := stableExtraT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let c1 := cC.rank 1+ec
    let t0 := cT.rank 0
    let t1 := cT.rank 1+et
    let o := (nonzeroProgram cC inp hDL).value
    Transports o.gates (ordinalIdentification (cC.rank 0) c1 t0 t1)
      (sourceHX (identityChecksOrdinal (degreeMatrix cC 0 1) ec))
      (targetHX (identityChecksOrdinal (degreeMatrix cT 0 1) et))
      (sourceZ (degreeMatrix cC (-1) 0)) (targetZ (degreeMatrix cT (-1) 0)) ∧
    LocalCircuit o.gates ∧ LocalPauliSemantics o.gates ∧
    ProductAncillaSemantics p (Fin t1 × Cells) ((Fin t0 ⊕ Fin c1) × Cells) ∧
    ProductAncillaSemantics p (Fin c1 × Cells) ((Fin (cC.rank 0) ⊕ Fin t1) × Cells) ∧
    o.sourceAncillas = sourceAncillaCount c1 t0 t1 ∧
    o.targetAncillas = targetAncillaCount (cC.rank 0) c1 t1 :=
  nonzeroProgram_physical cC (original.toPipeline cC) hDL Cells

end
end Decoupling.HighDim.AlgorithmTwoPipeline
