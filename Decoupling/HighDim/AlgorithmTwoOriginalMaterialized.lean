import Decoupling.HighDim.AlgorithmTwoBackendOriginalNativeValid
import Decoupling.HighDim.AlgorithmTwoMaterializedCost

/-!
# Original native input supplies the public finite-vector program

Materialization retains the exact original coefficient arrays up to
natural-number dimension casts. Backend validity is proved through the
explicit cochain isomorphism to the original complex. It is not an
additional code hypothesis or an intermediate algorithm certificate.
-/
namespace Decoupling.HighDim.AlgorithmTwoBackendOriginal
open AlgorithmTwoPipelineBackend
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
  (inp : AlgorithmTwoOriginalArrays.Input (D := D) (L := L) (h := h) coords)

def materializedInput : MaterializedInput K D L h := (rawInput coords inp).materialize

theorem materialized_valid : Valid (materializedInput coords inp).toRaw := by
  rw [materializedInput,RawInput.materialize_toRaw]
  exact raw_valid coords inp

theorem materialized_coefficientCount :
    (materializedInput coords inp).coefficientCount =
      AlgorithmTwoOriginalArrays.coefficientCount (D := D) (L := L) (h := h) coords := by
  rw [← MaterializedInput.toRaw_coefficientCount,materializedInput,RawInput.materialize_toRaw]
  unfold coefficientCount AlgorithmTwoOriginalArrays.coefficientCount
  apply Finset.sum_congr rfl
  intro i _
  rw [rawInput_rankAt,rawInput_rankAt]

end Decoupling.HighDim.AlgorithmTwoBackendOriginal

namespace Decoupling.HighDim.AlgorithmTwoBackendOriginal
open AlgorithmTwoPipelineBackend
variable {K : Type} [Field K] [DecidableEq K] {D h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-((D+2 : ℕ):ℤ))] [C.IsStrictlyLE ((D+2 : ℕ):ℤ)]
  (inp : AlgorithmTwoOriginalArrays.Input (D := D) (L := D+2) (h := h) coords)

/-- Complete public execution from the original arrays, with all backend
validity premises discharged from the original input itself. -/
theorem original_materialized_cost (hD : 2 ≤ D) :
    let a := materializedInput coords inp
    let run := executeMaterialized a (materialized_valid coords inp) (by omega : D ≤ D+2)
    let N := AlgorithmTwoOriginalArrays.coefficientCount (D := D) (L := D+2) (h := h) coords
    let B := (AlgorithmTwoResourceBudget.paperPolynomial D).eval N
    run.cost ≤ B ∧ run.value.gates.length ≤ B ∧ run.value.sourceAncillas ≤ B ∧
      run.value.targetAncillas ≤ B ∧ run.value.species ≤ B := by
  have hr := materialized_polynomial_cost (materializedInput coords inp) (materialized_valid coords inp) hD
  rw [materialized_coefficientCount] at hr
  exact hr

end Decoupling.HighDim.AlgorithmTwoBackendOriginal
