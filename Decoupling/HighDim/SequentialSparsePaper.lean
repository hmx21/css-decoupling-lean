import Decoupling.HighDim.SequentialSparsePhysical

/- HD016: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of Algorithm 2”.
New sequential-contraction execution; historical SparseCircuitPaper is preserved. -/
/-!
# HD016 paper-facing sparse Algorithm 2 endpoints

Original validity is the only semantic premise. Every coefficient remains
materialized finite data. The corrected common polynomial counts the new
zero tests as well as the original execution, and includes actual SWAP depth.
-/
namespace Decoupling.HighDim.SequentialSparseCircuit
open AlgorithmTwoPipeline AlgorithmTwoPipelineBackend AlgorithmTwo
open SequentialPipeline
open SequentialBackend
open SparseCircuit
open CategoryTheory HomologicalComplex AlgorithmTwoPipeline AlgorithmTwoPipelineBackend
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
variable (a : MaterializedInput K D L h) (valid : Valid a.toRaw) (hDL : D ≤ L)

theorem materialized_nativeEquivalence :
    Nonempty (HomotopyEquiv
      (AlgorithmTwoToricData.nativeStack D (materializedProgram a valid hDL).value.multiplicities K)
      (model a.toRaw valid)) := by
  rw [materialized_value]
  exact SequentialBackend.executeMaterialized_nativeEquivalence hDL a valid

theorem materialized_multiplicities (j : Fin (D-1)) :
    (materializedProgram a valid hDL).value.multiplicities.get j =
      Module.finrank K (Layers.coefficients ((model a.toRaw valid).homology (j.val+1))) := by
  rw [materialized_value]
  exact SequentialBackend.executeMaterialized_multiplicities hDL a valid j

theorem materialized_onsite :
    ∀ g ∈ (materializedProgram a valid hDL).value.gates, isSwap g = true →
      ∀ cell, (g.source cell).2 = cell ∧ (g.destination cell).2 = cell := by
  intro g _ hg cell
  exact OnSiteSwap.onsite_of_isSwap g hg cell

theorem proposition_one_sparse (D : ℕ) (hD : 2 ≤ D) :
    ∃ P : Polynomial ℕ,
      ∀ (K : Type) [Field K] [DecidableEq K] (h : ℕ)
        (a : MaterializedInput K D (D+2) h) (valid : Valid a.toRaw),
        let run := materializedProgram a valid (Nat.le_add_right D 2)
        run.cost ≤ P.eval a.coefficientCount ∧
          run.value.gates.length ≤ P.eval a.coefficientCount ∧
          run.value.sourceAncillas ≤ P.eval a.coefficientCount ∧
          run.value.targetAncillas ≤ P.eval a.coefficientCount := by
  refine ⟨SequentialResourceBudget.paperPolynomial D + SequentialResourceBudget.paperPolynomial D,?_⟩
  intro K instK instDec h a valid
  have hb := materialized_polynomial_cost a valid hD
  exact ⟨hb.1,hb.2.1,hb.2.2.1,hb.2.2.2.1⟩

end
end Decoupling.HighDim.SequentialSparseCircuit
