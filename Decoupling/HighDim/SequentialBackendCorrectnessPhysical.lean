import Decoupling.HighDim.AlgorithmTwoBackendCorrectnessPhysical
import Decoupling.HighDim.SequentialBackendCorrectness
import Decoupling.HighDim.SequentialPipelineCorrectnessQudit

/- HD016: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of Algorithm 2”.
New sequential-contraction execution; historical AlgorithmTwoBackendCorrectnessPhysical is preserved. -/
/-!
# Physical correctness of both finite-data execution branches

The two predicates below describe concrete checks and the actual returned
Work object. They are proved from the original finite input and its validity;
they are not new assumptions or supplied gate certificates. Whole-Work
equalities avoid a change of physical ordinal coordinates hidden in a cast.
The zero branch uses the actual zero native source and actual empty toric
target. The nonzero branch uses the computed target and literal ancilla blocks.
-/
namespace Decoupling.HighDim.SequentialBackend
open AlgorithmTwoPipeline AlgorithmTwoPipelineBackend AlgorithmTwo
open SequentialPipeline
open CategoryTheory CategoryTheory.Limits HomologicalComplex ArithmeticCost
open AlgorithmTwoPipeline AlgorithmTwoPhysicalTransport PhysicalIsomorphism
open AlgorithmTwoFiniteComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section

variable {p D L h : ℕ} [Fact p.Prime]
variable (raw : RawInput (ZMod p) D L h) (valid : Valid raw) (hDL : D ≤ L)
variable (Cells : Type*) [Fintype Cells] [DecidableEq Cells]

/-- Literal empty output and both actual native stabilizer modules on zero
physical coordinates. All metadata is fixed by the whole-output equality. -/
structure ZeroPhysicalOutput : Prop where
  emptyRank : storedRank raw = 0
  output_eq : execute raw valid hDL = AlgorithmTwo.emptyProgram (ZMod p) D
  transports :
    Transports (AlgorithmTwo.emptyProgram (ZMod p) D).value.gates (Equiv.refl (Fin 0))
      (degreeMatrix (emptySourceCoordinates raw valid emptyRank) 0 1)
      (degreeMatrix (emptyTargetCoordinates (ZMod p) D) 0 1)
      (degreeMatrix (emptySourceCoordinates raw valid emptyRank) (-1) 0)
      (degreeMatrix (emptyTargetCoordinates (ZMod p) D) (-1) 0)
  locality : LocalCircuit (AlgorithmTwo.emptyProgram (ZMod p) D).value.gates
  pauli : LocalPauliSemantics (AlgorithmTwo.emptyProgram (ZMod p) D).value.gates
  sourceAncillas : ProductAncillaSemantics p (Fin 0 × Cells) (Fin 0 × Cells)
  targetAncillas : ProductAncillaSemantics p (Fin 0 × Cells) (Fin 0 × Cells)

/-- Concrete nonempty-branch specification. The equality concerns the entire
actual Work value and trace; the physical fields concern its very gate list. -/
structure NonzeroPhysicalOutput : Prop where
  nonemptyRank : storedRank raw ≠ 0
  output_eq : execute raw valid hDL =
    SequentialPipeline.nonzeroProgram (modelCoordinates raw valid)
      ((modelInput raw valid).toPipeline (modelCoordinates raw valid)) hDL
  physical :
    let cC := modelCoordinates raw valid
    let inp := (modelInput raw valid).toPipeline cC
    let q := (SequentialPipeline.stagesProgram cC inp hDL).value
    let cT := originalFromFrame
      (AlgorithmTwoToricData.totalCoordinates D q.layers.multiplicities (ZMod p))
    let ec := SequentialPipeline.stableExtraC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let et := SequentialPipeline.stableExtraT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let c1 := cC.rank 1+ec
    let t0 := cT.rank 0
    let t1 := cT.rank 1+et
    let o := (SequentialPipeline.nonzeroProgram cC inp hDL).value
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
    let cC := modelCoordinates raw valid
    let inp := (modelInput raw valid).toPipeline cC
    let q := (SequentialPipeline.stagesProgram cC inp hDL).value
    let ec := SequentialPipeline.stableExtraC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let et := SequentialPipeline.stableExtraT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let c1 := cC.rank 1+ec
    let t0 := SequentialPipeline.targetRank cC inp hDL q.layers 0
    let t1 := SequentialPipeline.targetRank cC inp hDL q.layers 1+et
    let o := (SequentialPipeline.nonzeroProgram cC inp hDL).value
    o.sourceQ = cC.rank 0 ∧ o.targetQ = t0 ∧
    o.sourcePlus = t1 ∧ o.sourceZero = t0+c1 ∧
    o.targetPlus = c1 ∧ o.targetZero = cC.rank 0+t1 ∧
    o.sourceIdentityChecks = ec ∧ o.targetIdentityChecks = et

theorem execute_zero_physical (hz : storedRank raw = 0) :
    ZeroPhysicalOutput raw valid hDL Cells where
  emptyRank := hz
  output_eq := execute_zero raw valid hDL hz
  transports := AlgorithmTwo.emptyProgram_transports _ _ _ _
  locality := AlgorithmTwo.emptyProgram_local
  pauli := localPauliSemantics _
  sourceAncillas := productAncillaSemantics _ _ _
  targetAncillas := productAncillaSemantics _ _ _

theorem execute_nonzero_physical (hz : storedRank raw ≠ 0) :
    NonzeroPhysicalOutput raw valid hDL Cells where
  nonemptyRank := hz
  output_eq := execute_nonzero raw valid hDL hz
  physical := SequentialPipeline.nonzeroProgram_physical (modelCoordinates raw valid)
    ((modelInput raw valid).toPipeline (modelCoordinates raw valid)) hDL Cells
  metadata := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Both branches are discharged internally from the same original data.
Neither branch asks the caller for any intermediate mathematical certificate. -/
theorem execute_physical_cases :
    ZeroPhysicalOutput raw valid hDL Cells ∨
      NonzeroPhysicalOutput raw valid hDL Cells := by
  by_cases hz : storedRank raw = 0
  · exact Or.inl (execute_zero_physical raw valid hDL Cells hz)
  · exact Or.inr (execute_nonzero_physical raw valid hDL Cells hz)

theorem execute_localPauli :
    LocalPauliSemantics (execute raw valid hDL).value.gates :=
  localPauliSemantics _

variable (a : MaterializedInput (ZMod p) D L h) (ha : Valid a.toRaw)

/-- `executeMaterialized` is definitionally the `execute` occurring in the
two whole-Work equalities of these specifications. All its coefficients
are already materialized in finite vectors. -/
theorem executeMaterialized_physical_cases :
    ZeroPhysicalOutput a.toRaw ha hDL Cells ∨
      NonzeroPhysicalOutput a.toRaw ha hDL Cells :=
  execute_physical_cases a.toRaw ha hDL Cells

theorem executeMaterialized_localPauli :
    LocalPauliSemantics (executeMaterialized a ha hDL).value.gates :=
  execute_localPauli a.toRaw ha hDL

end
end Decoupling.HighDim.SequentialBackend
