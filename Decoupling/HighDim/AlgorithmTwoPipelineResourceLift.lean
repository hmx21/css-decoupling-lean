import Decoupling.HighDim.AlgorithmTwoPipelineResourceStable
import Decoupling.HighDim.AlgorithmTwoInvertibleGrowthPrograms

/-! # Final lift/circuit resources from actual C4 dimensions
All rank and radius bounds are discharged from the original input. The
solvability proof in the helper below is the native algebraic certificate
of the supplied C4 output; it supplies neither matrices nor cost bounds.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipelineResource
noncomputable section
open HomologicalComplex
open AlgorithmTwoPipeline AlgorithmTwoResourceBudget AlgorithmTwoInputGrowth
open StableFree.Effective.CochainProgram AlgorithmTwoInvertible ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
  (inp : Input (D := D) (L := L) (h := h) coords) (hDL : D ≤ L)
  (out : InputLayers coords inp hDL)
  (arrays : NativeArrays K D (inputRank coords L)
    (AlgorithmTwoToricData.totalRank D out.multiplicities) (nativeRadius coords inp hDL out))

abbrev StableOutput := Output K D (coords.rank 1) (coords.rank 0)
  ((targetOriginal coords inp hDL out).rank 1) ((targetOriginal coords inp hDL out).rank 0)
  (extraC coords inp hDL out arrays) (extraT coords inp hDL out arrays)
  (stableRadius coords inp hDL out arrays)

omit [DecidableEq K] in
theorem original_lower_stable : coords.rank 0 ≤ stable D L (inputBudget (L := L) (h := h) coords) :=
  (original_term_cone coords 0).trans (cone_le_stable D L _)

theorem target_lower_stable : (targetOriginal coords inp hDL out).rank 0 ≤
    stable D L (inputBudget (L := L) (h := h) coords) :=
  (target_term_cone coords inp hDL out 0).trans (cone_le_stable D L _)

theorem original_check_stable : coords.rank 1+extraC coords inp hDL out arrays ≤
    stable D L (inputBudget (L := L) (h := h) coords) :=
  (stable_output_ranks coords inp hDL out arrays).2.2.1

theorem target_check_stable : (targetOriginal coords inp hDL out).rank 1+extraT coords inp hDL out arrays ≤
    stable D L (inputBudget (L := L) (h := h) coords) :=
  (stable_output_ranks coords inp hDL out arrays).2.2.2

variable (v : StableOutput coords inp hDL out arrays)
  (hv : FourSolvable (LaurentArithmetic.matrixDenote v.dC) (LaurentArithmetic.matrixDenote v.dT)
    (LaurentArithmetic.matrixDenote v.forward) (LaurentArithmetic.matrixDenote v.inverse))

theorem output_lift_cost : (liftMatricesProgram v.dC v.dT v.forward v.inverse hv).cost ≤
    lift D L (inputBudget (L := L) (h := h) coords) := by
  rw [lift_eq, ← AlgorithmTwoInvertibleGrowth.polynomial_eval]
  exact AlgorithmTwoInvertibleGrowth.liftMatricesProgram_cost_polynomial _ _ _ _ _
    (original_lower_stable coords) (original_check_stable coords inp hDL out arrays)
    (target_lower_stable coords inp hDL out) (target_check_stable coords inp hDL out arrays)
    (stable_output_radius coords inp hDL out arrays)

theorem output_lift_radius :
    liftBox D (coords.rank 1+extraC coords inp hDL out arrays)
      ((targetOriginal coords inp hDL out).rank 0)
      ((targetOriginal coords inp hDL out).rank 1+extraT coords inp hDL out arrays)
      (coords.rank 0) (stableRadius coords inp hDL out arrays) ≤
      lift D L (inputBudget (L := L) (h := h) coords) := by
  rw [lift_eq]
  exact AlgorithmTwoInvertibleGrowth.liftBox_le (original_lower_stable coords)
    (original_check_stable coords inp hDL out arrays) (target_lower_stable coords inp hDL out)
    (target_check_stable coords inp hDL out arrays) (stable_output_radius coords inp hDL out arrays)

theorem output_lift_and_theta_cost :
    (Work.bind (liftMatricesProgram v.dC v.dT v.forward v.inverse hv) fun w =>
      DenseCircuitPermutation.canonicalThetaProgram w.psiHat w.phiHat).cost ≤
      lift D L (inputBudget (L := L) (h := h) coords) := by
  rw [lift_eq, ← AlgorithmTwoInvertibleGrowth.polynomial_eval]
  exact AlgorithmTwoInvertibleGrowth.lift_and_theta_cost_polynomial _ _ _ _ _
    (original_lower_stable coords) (original_check_stable coords inp hDL out arrays)
    (target_lower_stable coords inp hDL out) (target_check_stable coords inp hDL out arrays)
    (stable_output_radius coords inp hDL out arrays)

theorem output_lift_and_theta_depth :
    (Work.bind (liftMatricesProgram v.dC v.dT v.forward v.inverse hv) fun w =>
      DenseCircuitPermutation.canonicalThetaProgram w.psiHat w.phiHat).value.length ≤
      lift D L (inputBudget (L := L) (h := h) coords) := by
  rw [lift_eq, ← AlgorithmTwoInvertibleGrowth.polynomial_eval]
  exact AlgorithmTwoInvertibleGrowth.lift_and_theta_length_polynomial _ _ _ _ _
    (original_lower_stable coords) (original_check_stable coords inp hDL out arrays)
    (target_lower_stable coords inp hDL out) (target_check_stable coords inp hDL out arrays)
    (stable_output_radius coords inp hDL out arrays)

abbrev LiftOutput := LiftMatrices K D (coords.rank 0) (coords.rank 1+extraC coords inp hDL out arrays)
  ((targetOriginal coords inp hDL out).rank 0)
  ((targetOriginal coords inp hDL out).rank 1+extraT coords inp hDL out arrays)
  (liftBox D (coords.rank 1+extraC coords inp hDL out arrays)
    ((targetOriginal coords inp hDL out).rank 0)
    ((targetOriginal coords inp hDL out).rank 1+extraT coords inp hDL out arrays)
    (coords.rank 0) (stableRadius coords inp hDL out arrays))

theorem output_theta_cost (w : LiftOutput coords inp hDL out arrays) :
    (DenseCircuitPermutation.canonicalThetaProgram w.psiHat w.phiHat).cost ≤
      lift D L (inputBudget (L := L) (h := h) coords) := by
  rw [lift_eq, ← AlgorithmTwoInvertibleGrowth.polynomial_eval]
  exact AlgorithmTwoInvertibleGrowth.theta_cost_polynomial
    (original_lower_stable coords) (original_check_stable coords inp hDL out arrays)
    (target_lower_stable coords inp hDL out) (target_check_stable coords inp hDL out arrays)
    (stable_output_radius coords inp hDL out arrays) w

theorem output_theta_depth (w : LiftOutput coords inp hDL out arrays) :
    (DenseCircuitPermutation.canonicalThetaProgram w.psiHat w.phiHat).value.length ≤
      lift D L (inputBudget (L := L) (h := h) coords) := by
  rw [lift_eq, ← AlgorithmTwoInvertibleGrowth.polynomial_eval]
  exact AlgorithmTwoInvertibleGrowth.theta_length_polynomial
    (original_lower_stable coords) (original_check_stable coords inp hDL out arrays)
    (target_lower_stable coords inp hDL out) (target_check_stable coords inp hDL out arrays)
    (stable_output_radius coords inp hDL out arrays) w

theorem physical_width :
    ((targetOriginal coords inp hDL out).rank 0+(coords.rank 1+extraC coords inp hDL out arrays))+
      (coords.rank 0+((targetOriginal coords inp hDL out).rank 1+extraT coords inp hDL out arrays)) ≤
      lift D L (inputBudget (L := L) (h := h) coords) := by
  rw [lift_eq, Nat.add_comm]
  exact AlgorithmTwoInvertibleGrowth.physical_species_le (original_lower_stable coords)
    (original_check_stable coords inp hDL out arrays) (target_lower_stable coords inp hDL out)
    (target_check_stable coords inp hDL out arrays)

/-- These are the actual source/target ancilla counts of the physical
adapter, not the C4 identity-check row counts extraC/extraT. -/
theorem source_ancilla_count :
    ((targetOriginal coords inp hDL out).rank 1+extraT coords inp hDL out arrays)+
      ((targetOriginal coords inp hDL out).rank 0+(coords.rank 1+extraC coords inp hDL out arrays)) ≤
      lift D L (inputBudget (L := L) (h := h) coords) := by
  have := physical_width coords inp hDL out arrays
  omega

theorem target_ancilla_count :
    (coords.rank 1+extraC coords inp hDL out arrays)+
      (coords.rank 0+((targetOriginal coords inp hDL out).rank 1+extraT coords inp hDL out arrays)) ≤
      lift D L (inputBudget (L := L) (h := h) coords) := by
  have := physical_width coords inp hDL out arrays
  omega

end
end Decoupling.HighDim.AlgorithmTwoPipelineResource
