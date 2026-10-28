import Decoupling.HighDim.AlgorithmTwoComputedLayersProgram
import Decoupling.HighDim.AlgorithmTwoCohomologyCost

/-!
# Materialized cohomology results shared by the full Algorithm 2 pipeline

The layer computations are executed once. A finite vector stores every
rank, radius, output dimension and cocycle coefficient array. Native
correctness witnesses refer to those same stored arrays; later stages
read the stored dimensions instead of rerunning cohomology computation.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipeline
open ArithmeticCost AlgorithmTwoCohomology
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D h : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}

structure StoredLayer (K : Type) (D : ℕ) where
  rank : ℕ
  radius : ℕ
  dimension : ℕ
  cocycles : LaurentArithmetic.DenseMatrix K D rank dimension radius

def packLayer {q B : ℕ} (r : Result K D q B) : StoredLayer K D :=
  ⟨q,B,r.dimension,r.cocycles⟩

def StoredLayer.toResult (s : StoredLayer K D) (q B : ℕ)
    (hq : s.rank=q) (hB : s.radius=B) : Result K D q B := by
  subst q
  subst B
  exact ⟨s.dimension,s.cocycles⟩

omit [Field K] [DecidableEq K] in
theorem StoredLayer.toResult_eq {q B : ℕ} (s : StoredLayer K D) (r : Result K D q B)
    (he : s = packLayer r) (hq : s.rank=q) (hB : s.radius=B) : s.toResult q B hq hB = r := by
  subst s
  rfl

omit [Field K] [DecidableEq K] in
theorem StoredLayer.toResult_dimension (s : StoredLayer K D) (q B : ℕ)
    (hq : s.rank=q) (hB : s.radius=B) : (s.toResult q B hq hB).dimension = s.dimension := by
  subst q
  subst B
  rfl

variable (cC : StableFree.Coordinates C)
  (b : ∀ j : Fin (D-1), LaurentArithmetic.DenseMatrix K D (cC.rank (j.val+1))
    (cC.rank ((j.val:ℤ)+1-1)) h)
  (d : ∀ j : Fin (D-1), LaurentArithmetic.DenseMatrix K D (cC.rank ((j.val:ℤ)+1+1))
    (cC.rank (j.val+1)) h)

def layerProgram : Work K (Vector (StoredLayer K D) (D-1)) :=
  collect (D-1) fun j => Work.bind (compute (b j) (d j)) fun out => Work.pure (packLayer out)

theorem layerProgram_get (j : Fin (D-1)) :
    (layerProgram cC b d).value[j] = packLayer (AlgorithmTwoComputedLayers.output cC b d j) := by
  simp only [layerProgram, collect_value_get, Work.bind_value, Work.pure_value, AlgorithmTwoComputedLayers.output]

theorem layerProgram_cost : (layerProgram cC b d).cost =
    ∑ j : Fin (D-1), (compute (b j) (d j)).cost := by
  simp only [layerProgram, collect_cost, Work.bind_cost, Work.pure_cost, add_zero]

theorem layerProgram_cost_bound : (layerProgram cC b d).cost ≤
    ∑ j : Fin (D-1), AlgorithmTwoCohomology.costBound D (cC.rank (j.val+1))
      (cC.rank ((j.val:ℤ)+1-1)) (cC.rank ((j.val:ℤ)+1+1)) h := by
  rw [layerProgram_cost]
  exact Finset.sum_le_sum fun j _ => compute_cost (b j) (d j)

/-- The proof field is established by the execution below, never supplied
as an algorithmic oracle. It relates stored data to the existing native
cohomology theorems without evaluating those theorems at runtime. -/
structure StoredLayers where
  data : Vector (StoredLayer K D) (D-1)
  correct : ∀ j, data[j] = packLayer (AlgorithmTwoComputedLayers.output cC b d j)

def storedLayersProgram : Work K (StoredLayers cC b d) :=
  let run := layerProgram cC b d
  { value := ⟨run.value, layerProgram_get cC b d⟩
    trace := run.trace }

@[simp] theorem storedLayersProgram_cost : (storedLayersProgram cC b d).cost = (layerProgram cC b d).cost := rfl

namespace StoredLayers
variable {cC b d}

def multiplicities (s : StoredLayers cC b d) : Vector ℕ (D-1) :=
  s.data.map StoredLayer.dimension

theorem multiplicities_get (s : StoredLayers cC b d) (j : Fin (D-1)) :
    s.multiplicities.get j = s.data[j].dimension := by
  change (s.data.map StoredLayer.dimension)[j.val] = _
  rw [Vector.getElem_map]
  rfl

theorem multiplicities_correct (s : StoredLayers cC b d) (j : Fin (D-1)) :
    (s.multiplicities).get j = AlgorithmTwoComputedLayers.outputMultiplicities cC b d j := by
  change (s.data.map StoredLayer.dimension)[j.val] = _
  rw [Vector.getElem_map]
  exact congrArg StoredLayer.dimension (s.correct j)

def result (s : StoredLayers cC b d) (j : Fin (D-1)) :
    Result K D (cC.rank (j.val+1)) (LaurentLinearSolver.outputBox D (cC.rank ((j.val:ℤ)+1+1)) h) :=
  (s.data[j]).toResult _ _ (congrArg StoredLayer.rank (s.correct j))
    (congrArg StoredLayer.radius (s.correct j))

theorem result_dimension (s : StoredLayers cC b d) (j : Fin (D-1)) :
    (s.result j).dimension = s.multiplicities.get j := by
  rw [multiplicities_get]
  exact StoredLayer.toResult_dimension _ _ _ _ _

theorem result_correct (s : StoredLayers cC b d) (j : Fin (D-1)) :
    s.result j = AlgorithmTwoComputedLayers.output cC b d j := by
  exact StoredLayer.toResult_eq _ _ (s.correct j) _ _

end StoredLayers
end Decoupling.HighDim.AlgorithmTwoPipeline
