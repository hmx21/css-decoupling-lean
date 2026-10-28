import Decoupling.HighDim.SchreyerAlgorithmOneMaterialized
import Decoupling.HighDim.SparseCircuitPaper

/-!
# HD014 the new Schreyer success model feeds the actual sparse Algorithm 2

The original hypotheses supply the represented coarse complex. The same
finite input is passed to the executable sparse backend, whose output
target and costs are proved. The input-size variable is that of this
coarse complex; no bound on its lattice index or input preparation is asserted.
-/
namespace Decoupling.HighDim.SchreyerAlgorithmOne
open CategoryTheory AlgorithmTwoPipelineBackend
noncomputable section
variable {p D q s r : ℕ} [Fact p.Prime] (c : CSS.Checks (ZMod p) D q s r)

theorem successComplex_sparseExecution_exists
    (hc : c.Topological) (hD : 2 ≤ D) (h : Layers.FiniteXLayers c) :
    ∃ B : ℕ, ∃ a : MaterializedInput (ZMod p) D (D+2) B,
      ∃ valid : Valid a.toRaw,
        Nonempty (successComplex c hc h ≅ AlgorithmTwoPipelineBackend.model a.toRaw valid) ∧
        (let run := SparseCircuit.materializedProgram a valid (Nat.le_add_right D 2)
         let P := AlgorithmTwoResourceBudget.paperPolynomial D
         let bound := (P+P).eval a.coefficientCount
         Nonempty (HomotopyEquiv
           (AlgorithmTwoToricData.nativeStack D run.value.multiplicities (ZMod p))
           (successComplex c hc h)) ∧
         run.cost ≤ bound ∧ run.value.gates.length ≤ bound ∧
         run.value.sourceAncillas ≤ bound ∧ run.value.targetAncillas ≤ bound) := by
  obtain ⟨B,a,valid,⟨e⟩⟩ := successComplex_materializedInput_exists c hc hD h
  obtain ⟨hE⟩ := SparseCircuit.materialized_nativeEquivalence a valid (Nat.le_add_right D 2)
  have hcost := SparseCircuit.materialized_polynomial_cost a valid hD
  exact ⟨B,a,valid,⟨e⟩,⟨hE.trans (HomotopyEquiv.ofIso e.symm)⟩,
    hcost.1,hcost.2.1,hcost.2.2.1,hcost.2.2.2.1⟩

end
end Decoupling.HighDim.SchreyerAlgorithmOne
