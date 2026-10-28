import Decoupling.HighDim.SparseCircuitProgram
import Decoupling.HighDim.OnSiteSwapPipeline
import Decoupling.HighDim.AlgorithmTwoMaterializedCost

/-!
# HD014 sparse physical output from actual materialized input

The original execution is evaluated once, then its returned gates are tested
and filtered. Every non-gate output field is copied. Test operations are fully
recorded; the new uniform polynomial is the sum of the old polynomial with itself.
-/
namespace Decoupling.HighDim.SparseCircuit
open Circuit ArithmeticCost AlgorithmTwoPipeline AlgorithmTwoPipelineBackend
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}

def output (o : RuntimeOutput K D) : RuntimeOutput K D := {o with gates := eraseZeroSUM o.gates}

def outputProgram (o : RuntimeOutput K D) : Work K (RuntimeOutput K D) :=
  Work.bind (eraseProgram o.gates) fun gates => Work.pure {o with gates := gates}

def postprocess (run : Work K (RuntimeOutput K D)) : Work K (RuntimeOutput K D) :=
  Work.bind run outputProgram

@[simp] theorem outputProgram_value (o : RuntimeOutput K D) : (outputProgram o).value = output o := by
  simp only [outputProgram,Work.bind_value,Work.pure_value,eraseProgram_value,output]

@[simp] theorem postprocess_value (run : Work K (RuntimeOutput K D)) :
    (postprocess run).value = output run.value := by simp only [postprocess,Work.bind_value,outputProgram_value]

theorem postprocess_trace (run : Work K (RuntimeOutput K D)) :
    (postprocess run).trace = run.trace ++ zeroTestTrace run.value.gates := by
  simp only [postprocess,outputProgram,Work.bind,Work.pure,List.append_nil,eraseProgram_trace]

theorem postprocess_cost (run : Work K (RuntimeOutput K D)) :
    (postprocess run).cost = run.cost + (zeroTestTrace run.value.gates).length := by
  simp only [Work.cost,postprocess_trace,List.length_append]

theorem postprocess_cost_le (run : Work K (RuntimeOutput K D)) :
    (postprocess run).cost ≤ run.cost + run.value.gates.length := by
  rw [postprocess_cost]
  exact Nat.add_le_add_left (zeroTestTrace_length_le _) _

theorem postprocess_arithmeticTrace (run : Work K (RuntimeOutput K D)) :
    arithmeticTrace (postprocess run).trace = arithmeticTrace run.trace := by
  rw [postprocess_trace,arithmeticTrace_append,arithmeticTrace_tests,List.append_nil]

/-- Complete finite-vector entry: no native mathematical objects enter runtime. -/
def materializedProgram (a : MaterializedInput K D L h) (valid : Valid a.toRaw) (hDL : D ≤ L) :
    Work K (RuntimeOutput K D) := postprocess (executeMaterialized a valid hDL)

variable (a : MaterializedInput K D L h) (valid : Valid a.toRaw) (hDL : D ≤ L)

theorem materialized_value : (materializedProgram a valid hDL).value =
    output (executeMaterialized a valid hDL).value := postprocess_value _

/-- All dimensions, state counts and identity-check counts retain their original meanings. -/
theorem materialized_metadata :
    let old := (executeMaterialized a valid hDL).value
    let o := (materializedProgram a valid hDL).value
    o.multiplicities = old.multiplicities ∧ o.species = old.species ∧
    o.sourceQ = old.sourceQ ∧ o.targetQ = old.targetQ ∧
    o.sourcePlus = old.sourcePlus ∧ o.sourceZero = old.sourceZero ∧
    o.targetPlus = old.targetPlus ∧ o.targetZero = old.targetZero ∧
    o.sourceIdentityChecks = old.sourceIdentityChecks ∧
    o.targetIdentityChecks = old.targetIdentityChecks ∧
    o.sourceAncillas = old.sourceAncillas ∧ o.targetAncillas = old.targetAncillas := by
  rw [materialized_value]
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem materialized_length_le : (materializedProgram a valid hDL).value.gates.length ≤
    (executeMaterialized a valid hDL).value.gates.length := by
  rw [materialized_value]
  exact length_le _

theorem materialized_swaps : swapCount (materializedProgram a valid hDL).value.gates ≤
    (materializedProgram a valid hDL).value.species := by
  rw [materialized_value]
  change swapCount (eraseZeroSUM _) ≤ _
  rw [swapCount_erase]
  exact OnSiteSwap.materialized_swaps hDL a valid

theorem materialized_trace : (materializedProgram a valid hDL).trace =
    (executeMaterialized a valid hDL).trace ++
      zeroTestTrace (executeMaterialized a valid hDL).value.gates := postprocess_trace _

theorem materialized_polynomial_cost (a : MaterializedInput K D (D+2) h)
    (valid : Valid a.toRaw) (hD : 2 ≤ D) :
    let run := materializedProgram a valid (Nat.le_add_right D 2)
    let P := AlgorithmTwoResourceBudget.paperPolynomial D
    let B := (P+P).eval a.coefficientCount
    run.cost ≤ B ∧ run.value.gates.length ≤ B ∧ run.value.sourceAncillas ≤ B ∧
      run.value.targetAncillas ≤ B ∧ run.value.species ≤ B := by
  have hb := AlgorithmTwoPipelineBackend.materialized_polynomial_cost a valid hD
  have hc := postprocess_cost_le (executeMaterialized a valid (Nat.le_add_right D 2))
  have hl := materialized_length_le a valid (Nat.le_add_right D 2)
  dsimp only at hb ⊢
  simp only [Polynomial.eval_add]
  rw [materialized_value]
  rw [materialized_value] at hl
  change _ ≤ _ ∧ _ ≤ _ ∧ (executeMaterialized a valid _).value.sourceAncillas ≤ _ ∧
    (executeMaterialized a valid _).value.targetAncillas ≤ _ ∧
    (executeMaterialized a valid _).value.species ≤ _
  exact ⟨hc.trans (Nat.add_le_add hb.1 hb.2.1),
    hl.trans (hb.2.1.trans (Nat.le_add_right _ _)),
    hb.2.2.1.trans (Nat.le_add_right _ _),
    hb.2.2.2.1.trans (Nat.le_add_right _ _),hb.2.2.2.2.trans (Nat.le_add_right _ _)⟩

end Decoupling.HighDim.SparseCircuit
