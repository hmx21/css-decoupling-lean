import Decoupling.HighDim.SparseCircuitOutput
import Decoupling.HighDim.SparseCircuitProgram
import Decoupling.HighDim.SequentialOnSiteSwapPipeline
import Decoupling.HighDim.SequentialMaterializedCost

/- HD016: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of Algorithm 2”.
New sequential-contraction execution; historical SparseCircuitOutput is preserved. -/
/-!
# HD016 sparse physical output from actual materialized input

The descending execution is evaluated once, then its returned gates are tested
and filtered. Every non-gate output field is copied. Test operations are fully
recorded; the sparse bound doubles the new descending dense-run polynomial.
-/
namespace Decoupling.HighDim.SequentialSparseCircuit
open AlgorithmTwoPipeline AlgorithmTwoPipelineBackend AlgorithmTwo
open SequentialPipeline
open SequentialBackend
open SparseCircuit
open Circuit ArithmeticCost AlgorithmTwoPipeline AlgorithmTwoPipelineBackend
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}

/-- Complete finite-vector entry: no native mathematical objects enter runtime. -/
def materializedProgram (a : MaterializedInput K D L h) (valid : Valid a.toRaw) (hDL : D ≤ L) :
    Work K (RuntimeOutput K D) := postprocess (SequentialBackend.executeMaterialized a valid hDL)

variable (a : MaterializedInput K D L h) (valid : Valid a.toRaw) (hDL : D ≤ L)

theorem materialized_value : (materializedProgram a valid hDL).value =
    output (SequentialBackend.executeMaterialized a valid hDL).value := postprocess_value _

/-- All dimensions, state counts and identity-check counts retain their original meanings. -/
theorem materialized_metadata :
    let old := (SequentialBackend.executeMaterialized a valid hDL).value
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
    (SequentialBackend.executeMaterialized a valid hDL).value.gates.length := by
  rw [materialized_value]
  exact length_le _

theorem materialized_swaps : swapCount (materializedProgram a valid hDL).value.gates ≤
    (materializedProgram a valid hDL).value.species := by
  rw [materialized_value]
  change swapCount (eraseZeroSUM _) ≤ _
  rw [swapCount_erase]
  exact SequentialOnSiteSwap.materialized_swaps hDL a valid

theorem materialized_trace : (materializedProgram a valid hDL).trace =
    (SequentialBackend.executeMaterialized a valid hDL).trace ++
      zeroTestTrace (SequentialBackend.executeMaterialized a valid hDL).value.gates := postprocess_trace _

theorem materialized_polynomial_cost (a : MaterializedInput K D (D+2) h)
    (valid : Valid a.toRaw) (hD : 2 ≤ D) :
    let run := materializedProgram a valid (Nat.le_add_right D 2)
    let P := SequentialResourceBudget.paperPolynomial D
    let B := (P+P).eval a.coefficientCount
    run.cost ≤ B ∧ run.value.gates.length ≤ B ∧ run.value.sourceAncillas ≤ B ∧
      run.value.targetAncillas ≤ B ∧ run.value.species ≤ B := by
  have hb := SequentialBackend.materialized_polynomial_cost a valid hD
  have hc := postprocess_cost_le (SequentialBackend.executeMaterialized a valid (Nat.le_add_right D 2))
  have hl := materialized_length_le a valid (Nat.le_add_right D 2)
  dsimp only at hb ⊢
  simp only [Polynomial.eval_add]
  rw [materialized_value]
  rw [materialized_value] at hl
  change _ ≤ _ ∧ _ ≤ _ ∧ (SequentialBackend.executeMaterialized a valid _).value.sourceAncillas ≤ _ ∧
    (SequentialBackend.executeMaterialized a valid _).value.targetAncillas ≤ _ ∧
    (SequentialBackend.executeMaterialized a valid _).value.species ≤ _
  exact ⟨hc.trans (Nat.add_le_add hb.1 hb.2.1),
    hl.trans (hb.2.1.trans (Nat.le_add_right _ _)),
    hb.2.2.1.trans (Nat.le_add_right _ _),
    hb.2.2.2.1.trans (Nat.le_add_right _ _),hb.2.2.2.2.trans (Nat.le_add_right _ _)⟩

end Decoupling.HighDim.SequentialSparseCircuit
