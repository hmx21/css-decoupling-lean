import Decoupling.HighDim.SparseCircuitOutput
import Decoupling.HighDim.SparseCircuitUnitary
import Decoupling.HighDim.AlgorithmTwoBackendCorrectnessPhysical

/-!
# HD014 physical correctness of the actual sparse materialized output

Both branches concern the executed test-and-filter postprocessor. The
nonzero branch's Work equality includes its appended zero-test trace;
its physical word is the filtered word, in the same ordinal coordinates.
-/
namespace Decoupling.HighDim.SparseCircuit
open CategoryTheory CategoryTheory.Limits HomologicalComplex ArithmeticCost
open AlgorithmTwoPipeline AlgorithmTwoPhysicalTransport PhysicalIsomorphism
open AlgorithmTwoFiniteComplex AlgorithmTwoPipelineBackend
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section

variable {p D L h : ℕ} [Fact p.Prime]
variable (a : MaterializedInput (ZMod p) D L h) (valid : Valid a.toRaw) (hDL : D ≤ L)
variable (Cells : Type*) [Fintype Cells] [DecidableEq Cells]

/-- Literal empty output and both actual native stabilizer modules on zero
physical coordinates. All metadata is fixed by the whole-output equality. -/
structure ZeroPhysicalOutput : Prop where
  emptyRank : storedRank a.toRaw = 0
  output_eq : materializedProgram a valid hDL = AlgorithmTwo.emptyProgram (ZMod p) D
  transports :
    Transports (AlgorithmTwo.emptyProgram (ZMod p) D).value.gates (Equiv.refl (Fin 0))
      (degreeMatrix (emptySourceCoordinates a.toRaw valid emptyRank) 0 1)
      (degreeMatrix (emptyTargetCoordinates (ZMod p) D) 0 1)
      (degreeMatrix (emptySourceCoordinates a.toRaw valid emptyRank) (-1) 0)
      (degreeMatrix (emptyTargetCoordinates (ZMod p) D) (-1) 0)
  locality : LocalCircuit (AlgorithmTwo.emptyProgram (ZMod p) D).value.gates
  pauli : LocalPauliSemantics (AlgorithmTwo.emptyProgram (ZMod p) D).value.gates
  sourceAncillas : ProductAncillaSemantics p (Fin 0 × Cells) (Fin 0 × Cells)
  targetAncillas : ProductAncillaSemantics p (Fin 0 × Cells) (Fin 0 × Cells)

/-- Concrete nonempty-branch specification. The equality concerns the entire
actual Work value and trace; the physical fields concern its very gate list. -/
structure NonzeroPhysicalOutput : Prop where
  nonemptyRank : storedRank a.toRaw ≠ 0
  output_eq : materializedProgram a valid hDL =
    postprocess (nonzeroProgram (modelCoordinates a.toRaw valid)
      ((modelInput a.toRaw valid).toPipeline (modelCoordinates a.toRaw valid)) hDL)
  physical :
    let cC := modelCoordinates a.toRaw valid
    let inp := (modelInput a.toRaw valid).toPipeline cC
    let q := (stagesProgram cC inp hDL).value
    let cT := originalFromFrame
      (AlgorithmTwoToricData.totalCoordinates D q.layers.multiplicities (ZMod p))
    let ec := stableExtraC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let et := stableExtraT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let c1 := cC.rank 1+ec
    let t0 := cT.rank 0
    let t1 := cT.rank 1+et
    let o := output (nonzeroProgram cC inp hDL).value
    Transports o.gates (ordinalIdentification (cC.rank 0) c1 t0 t1)
      (sourceHX (identityChecksOrdinal (degreeMatrix cC 0 1) ec))
      (targetHX (identityChecksOrdinal (degreeMatrix cT 0 1) et))
      (sourceZ (degreeMatrix cC (-1) 0)) (targetZ (degreeMatrix cT (-1) 0)) ∧
    LocalCircuit o.gates ∧ LocalPauliSemantics o.gates ∧
    ProductAncillaSemantics p (Fin t1 × Cells) ((Fin t0 ⊕ Fin c1) × Cells) ∧
    ProductAncillaSemantics p (Fin c1 × Cells) ((Fin (cC.rank 0) ⊕ Fin t1) × Cells) ∧
    o.sourceAncillas = sourceAncillaCount c1 t0 t1 ∧
    o.targetAncillas = targetAncillaCount (cC.rank 0) c1 t1
  metadata :
    let cC := modelCoordinates a.toRaw valid
    let inp := (modelInput a.toRaw valid).toPipeline cC
    let q := (stagesProgram cC inp hDL).value
    let ec := stableExtraC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let et := stableExtraT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let c1 := cC.rank 1+ec
    let t0 := targetRank cC inp hDL q.layers 0
    let t1 := targetRank cC inp hDL q.layers 1+et
    let o := output (nonzeroProgram cC inp hDL).value
    o.sourceQ = cC.rank 0 ∧ o.targetQ = t0 ∧
    o.sourcePlus = t1 ∧ o.sourceZero = t0+c1 ∧
    o.targetPlus = c1 ∧ o.targetZero = cC.rank 0+t1 ∧
    o.sourceIdentityChecks = ec ∧ o.targetIdentityChecks = et

  sparse_depth :
    let cC := modelCoordinates a.toRaw valid
    let inp := (modelInput a.toRaw valid).toPipeline cC
    let q := (stagesProgram cC inp hDL).value
    let w := (liftProgram cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction q.stable).value
    let old := (nonzeroProgram cC inp hDL).value
    (output old).gates.length ≤ Circuit.supportSize (LaurentArithmetic.matrixDenote w.psiHat) +
      Circuit.supportSize (LaurentArithmetic.matrixDenote w.phiHat) + old.species

theorem materialized_zero_physical (hz : storedRank a.toRaw = 0) :
    ZeroPhysicalOutput a valid hDL Cells where
  emptyRank := hz
  output_eq := by
    change postprocess (execute a.toRaw valid hDL) = _
    rw [execute_zero a.toRaw valid hDL hz]
    rfl
  transports := AlgorithmTwo.emptyProgram_transports _ _ _ _
  locality := AlgorithmTwo.emptyProgram_local
  pauli := localPauliSemantics _
  sourceAncillas := productAncillaSemantics _ _ _
  targetAncillas := productAncillaSemantics _ _ _

theorem materialized_nonzero_physical (hz : storedRank a.toRaw ≠ 0) :
    NonzeroPhysicalOutput a valid hDL Cells where
  nonemptyRank := hz
  output_eq := by
    change postprocess (execute a.toRaw valid hDL) = _
    rw [execute_nonzero a.toRaw valid hDL hz]
  physical := by
    have ht := nonzeroProgram_physical (modelCoordinates a.toRaw valid)
      ((modelInput a.toRaw valid).toPipeline (modelCoordinates a.toRaw valid)) hDL Cells
    exact ⟨transports_erase _ _ _ _ _ _ ht.1,localCircuit _,localPauliSemantics _,
      ht.2.2.2.1,ht.2.2.2.2.1,ht.2.2.2.2.2.1,ht.2.2.2.2.2.2⟩
  metadata := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  sparse_depth := by
    let cC := modelCoordinates a.toRaw valid
    let inp := (modelInput a.toRaw valid).toPipeline cC
    let q := (stagesProgram cC inp hDL).value
    let w := (liftProgram cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction q.stable).value
    apply (canonicalTheta_sparse_length w.psiHat w.phiHat).trans
    let n := targetRank cC inp hDL q.layers 0 +
      (cC.rank 1+stableExtraC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction)
    let m := cC.rank 0 +
      (targetRank cC inp hDL q.layers 1+stableExtraT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction)
    change Circuit.supportSize (LaurentArithmetic.matrixDenote w.psiHat) +
      Circuit.supportSize (LaurentArithmetic.matrixDenote w.phiHat) + n + m ≤
      Circuit.supportSize (LaurentArithmetic.matrixDenote w.psiHat) +
      Circuit.supportSize (LaurentArithmetic.matrixDenote w.phiHat) + (n+m)
    omega

/-- Both branches are discharged internally from the same original data.
Neither branch asks the caller for any intermediate mathematical certificate. -/
theorem materialized_physical_cases :
    ZeroPhysicalOutput a valid hDL Cells ∨
      NonzeroPhysicalOutput a valid hDL Cells := by
  by_cases hz : storedRank a.toRaw = 0
  · exact Or.inl (materialized_zero_physical a valid hDL Cells hz)
  · exact Or.inr (materialized_nonzero_physical a valid hDL Cells hz)

theorem materialized_localPauli :
    LocalPauliSemantics (materializedProgram a valid hDL).value.gates :=
  localPauliSemantics _

theorem materialized_local :
    LocalCircuit (materializedProgram a valid hDL).value.gates := localCircuit _

end
end Decoupling.HighDim.SparseCircuit
