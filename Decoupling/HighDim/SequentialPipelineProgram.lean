import Decoupling.HighDim.SequentialPipelineStableOutput
import Decoupling.HighDim.AlgorithmTwoPipelineOutput
import Decoupling.HighDim.DenseCircuitPermutationTheta

/- HD016: appendix.tex C4 “Inverting Γ up to homotopy” and C5 “The lines of Algorithm 2”.
New sequential-contraction execution; historical AlgorithmTwoPipelineProgram is preserved. -/
/-!
# Algorithm 2: one executable array-to-SUM/SWAP pipeline

Stored values share each computed cohomology basis, target differential,
comparison, cone contraction, C4 output and invertible lift. Every executed
field operation appears once in the concatenated trace. The only semantic
input is the original finite complex's split profile, supplied upstream by
Algorithm 1; no intermediate maps, homotopies or solver certificates are inputs.
-/
namespace Decoupling.HighDim.SequentialPipeline
open AlgorithmTwoPipeline
open ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
variable (inp : Input (D := D) (L := L) (h := h) cC) (hDL : D ≤ L)

structure Stages where
  layers : InputLayers cC inp hDL
  target : StoredTarget cC inp hDL layers
  gamma : StoredGamma cC inp hDL layers target
  homotopy : StoredHomotopy cC inp hDL layers target gamma
  extraction : StoredExtraction cC inp hDL layers target gamma homotopy
  stable : StoredStable cC inp hDL layers target gamma homotopy extraction

/-- The six stages before the four invertible lifts, each evaluated once. -/
def stagesProgram : Work K (Stages cC inp hDL) :=
  Work.bind (computeLayers cC inp hDL) fun s =>
  Work.bind (storeTargetProgram cC inp hDL s) fun t =>
  Work.bind (gammaProgram cC inp hDL s t) fun g =>
  Work.bind (homotopyProgram cC inp hDL s t g) fun H =>
  Work.bind (extractionProgram cC inp hDL s t g H) fun x =>
  Work.bind (storeStableProgram cC inp hDL s t g H x) fun u =>
  Work.pure ⟨s,t,g,H,x,u⟩

/-- Actual four lifts and the canonical physical word in the C-to-T direction. -/
def finishProgram (q : Stages cC inp hDL) : Work K (RuntimeOutput K D) :=
  let out := liftProgram cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction q.stable
  let circuit := DenseCircuitPermutation.canonicalThetaProgram out.value.psiHat out.value.phiHat
  let c0 := cC.rank 0
  let t0 := targetRank cC inp hDL q.layers 0
  let c1 := cC.rank 1+stableExtraC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
  let t1 := targetRank cC inp hDL q.layers 1+stableExtraT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
  { value := {
      multiplicities := q.layers.multiplicities
      species := (t0+c1)+(c0+t1)
      gates := circuit.value
      sourceQ := c0
      targetQ := t0
      sourcePlus := t1
      sourceZero := t0+c1
      targetPlus := c1
      targetZero := c0+t1
      sourceIdentityChecks := stableExtraC cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction
      targetIdentityChecks := stableExtraT cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction }
    trace := out.trace ++ circuit.trace }

/-- The nonzero-input branch used by the paper-size wrapper. Its computation
also makes sense on zero input; the outer wrapper bypasses it in that case. -/
def nonzeroProgram : Work K (RuntimeOutput K D) :=
  Work.bind (stagesProgram cC inp hDL) (finishProgram cC inp hDL)

theorem nonzeroProgram_cost : (nonzeroProgram cC inp hDL).cost =
    (stagesProgram cC inp hDL).cost + (finishProgram cC inp hDL (stagesProgram cC inp hDL).value).cost :=
  Work.bind_cost _ _

theorem finishProgram_cost (q : Stages cC inp hDL) :
    (finishProgram cC inp hDL q).cost =
      (liftProgram cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction q.stable).cost +
      (DenseCircuitPermutation.canonicalThetaProgram
        (liftProgram cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction q.stable).value.psiHat
        (liftProgram cC inp hDL q.layers q.target q.gamma q.homotopy q.extraction q.stable).value.phiHat).cost := by
  simp only [finishProgram,Work.cost,List.length_append]

theorem finishProgram_species (q : Stages cC inp hDL) :
    let o := (finishProgram cC inp hDL q).value
    o.sourceQ+o.sourceAncillas=o.species ∧ o.targetQ+o.targetAncillas=o.species := by
  dsimp [finishProgram,RuntimeOutput.sourceAncillas,RuntimeOutput.targetAncillas]
  omega

end Decoupling.HighDim.SequentialPipeline
