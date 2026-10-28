import Decoupling.HighDim.SequentialPipelineProgram
import Decoupling.HighDim.AlgorithmTwoEmptyProgram
import Decoupling.HighDim.AlgorithmTwoInputZero

/- HD016: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of Algorithm 2”.
New sequential-contraction execution; historical AlgorithmTwoProgram is preserved. -/
/-!
# HD016 complete execution from the original adjacent differential arrays

The zero-total-rank branch returns an empty physical output immediately.
The nonzero branch assembles the original arrays by pure copying and
executes the proved layer/comparison/cone/C4/lift/circuit pipeline.
No intermediate solver or cost certificate is supplied by the caller.
-/
namespace Decoupling.HighDim.SequentialAlgorithmTwo
open AlgorithmTwoPipeline AlgorithmTwo
open SequentialPipeline
open ArithmeticCost AlgorithmTwoPipeline
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
  (inp : AlgorithmTwoOriginalArrays.Input (D := D) (L := L) (h := h) coords)
  (hDL : D ≤ L)

def program : Work K (RuntimeOutput K D) :=
  if inputRank coords L = 0 then AlgorithmTwo.emptyProgram K D
  else Work.bind (inp.program coords) fun inner => SequentialPipeline.nonzeroProgram coords inner hDL

theorem program_zero (hz : inputRank coords L = 0) :
    program coords inp hDL = AlgorithmTwo.emptyProgram K D := by
  rw [program,ite_eq_left hz]

theorem program_nonzero (hz : inputRank coords L ≠ 0) :
    program coords inp hDL = SequentialPipeline.nonzeroProgram coords (inp.toPipeline coords) hDL := by
  rw [program,ite_eq_right hz]
  rfl

theorem program_zero_resources (hz : inputRank coords L = 0) :
    (program coords inp hDL).cost = 0 ∧
      (program coords inp hDL).value.gates.length = 0 ∧
      (program coords inp hDL).value.sourceAncillas = 0 ∧
      (program coords inp hDL).value.targetAncillas = 0 := by
  rw [program_zero coords inp hDL hz]
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem program_zero_input (hD : 0 < D)
    (hz : AlgorithmTwoOriginalArrays.coefficientCount (D := D) (L := L) (h := h) coords = 0) :
    program coords inp hDL = AlgorithmTwo.emptyProgram K D :=
  program_zero coords inp hDL ((inp.total_zero_iff coords hD).mpr hz)

omit [DecidableEq K] in
theorem program_zero_native (hz : inputRank coords L = 0) :
    Nonempty (HomotopyEquiv C (emptyTarget K D)) :=
  emptyProgram_native coords hz

end Decoupling.HighDim.SequentialAlgorithmTwo
