import Decoupling.HighDim.AlgorithmTwoBackendCorrectness
import Decoupling.HighDim.AlgorithmTwoPipelineCorrectnessQudit

/-!
# Physical correctness of both finite-data execution branches

The two predicates below describe concrete checks and the actual returned
Work object. They are proved from the original finite input and its validity;
they are not new assumptions or supplied gate certificates. Whole-Work
equalities avoid a change of physical ordinal coordinates hidden in a cast.
The zero branch uses the actual zero native source and actual empty toric
target. The nonzero branch uses the computed target and literal ancilla blocks.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipelineBackend
open CategoryTheory CategoryTheory.Limits HomologicalComplex ArithmeticCost
open AlgorithmTwoPipeline AlgorithmTwoPhysicalTransport PhysicalIsomorphism
open AlgorithmTwoFiniteComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section

section ZeroCoordinates
variable {K : Type} [Field K] {D L h : ℕ}
variable (raw : RawInput K D L h) (valid : Valid raw)

/-- Coordinates on the genuine native source when every stored rank is zero. -/
def emptySourceCoordinates (hz : storedRank raw = 0) : StableFree.Coordinates (model raw valid) where
  rank _ := 0
  equiv j := by
    let : Subsingleton ((model raw valid).X j) :=
      term_subsingleton_of_total_zero (modelCoordinates raw valid)
        ((coordinates_inputRank raw (Classical.choose valid)).trans hz) j
    exact LinearEquiv.ofSubsingleton _ _

/-- Coordinates on the actual empty toric complex, not an arbitrary zero model. -/
def emptyTargetCoordinates (K : Type) [Field K] (D : ℕ) :
    StableFree.Coordinates (emptyTarget K D) where
  rank _ := 0
  equiv j := by
    let : Subsingleton ((emptyTarget K D).X j) := emptyTarget_term_subsingleton j
    exact LinearEquiv.ofSubsingleton _ _
end ZeroCoordinates

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
    nonzeroProgram (modelCoordinates raw valid)
      ((modelInput raw valid).toPipeline (modelCoordinates raw valid)) hDL
  physical :
    let cC := modelCoordinates raw valid
    let inp := (modelInput raw valid).toPipeline cC
    let q := (stagesProgram cC inp hDL).value
    let cT := originalFromFrame
      (AlgorithmTwoToricData.totalCoordinates D q.layers.multiplicities (ZMod p))
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
    o.targetAncillas = targetAncillaCount (cC.rank 0) c1 t1
  metadata :
    let cC := modelCoordinates raw valid
    let inp := (modelInput raw valid).toPipeline cC
    let q := (stagesProgram cC inp hDL).value
    let ec := stableExtraC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let et := stableExtraT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
    let c1 := cC.rank 1+ec
    let t0 := targetRank cC inp hDL q.layers 0
    let t1 := targetRank cC inp hDL q.layers 1+et
    let o := (nonzeroProgram cC inp hDL).value
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
  physical := nonzeroProgram_physical (modelCoordinates raw valid)
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
end Decoupling.HighDim.AlgorithmTwoPipelineBackend
