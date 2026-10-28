import Decoupling.HighDim.AlgorithmTwoInvertibleGrowth

/-! # Uniform bounds on the executed lift and SUM/SWAP compilation
The combined bound counts the trace of the actual bind, not a hypothetical
algorithm. Word length includes the compiled physical ordinal SWAPs.
The order is psiHat then phiHat, namely the C-to-T matrix U;
the opposite order would compile its inverse.
-/
namespace Decoupling.HighDim.AlgorithmTwoInvertibleGrowth
open ArithmeticCost AlgorithmTwoInvertible LaurentArithmetic DenseCircuitPermutation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] [DecidableEq K] {D c0 c1 t0 t1 h s : ℕ}
variable (dC : DenseMatrix K D c1 c0 h) (dT : DenseMatrix K D t1 t0 h)
  (F : DenseMatrix K D c1 t1 h) (G : DenseMatrix K D t1 c1 h)
  (hs : FourSolvable (matrixDenote dC) (matrixDenote dT) (matrixDenote F) (matrixDenote G))

variable (hc0 : c0 ≤ s) (hc1 : c1 ≤ s) (ht0 : t0 ≤ s) (ht1 : t1 ≤ s) (hh : h ≤ s)
include hc0 hc1 ht0 ht1 hh

theorem fourProgram_cost_polynomial : (fourProgram dC dT F G hs).cost ≤ (polynomial D).eval s := by
  rw [polynomial_eval]
  have h₀ := (fourProgram_cost dC dT F G hs).trans (fourCost_le hc0 hc1 ht0 ht1 hh)
  unfold bound
  omega

theorem liftMatricesProgram_cost_polynomial :
    (liftMatricesProgram dC dT F G hs).cost ≤ (polynomial D).eval s := by
  rw [polynomial_eval]
  have h₀ := (liftMatricesProgram_cost dC dT F G hs).trans (liftMatricesCost_le hc0 hc1 ht0 ht1 hh)
  unfold bound
  omega

omit [DecidableEq K] in
theorem theta_cost_cap (v : LiftMatrices K D c0 c1 t0 t1 (liftBox D c1 t0 t1 c0 h)) :
    (canonicalThetaProgram v.psiHat v.phiHat).cost ≤ 3*outputCap D s := by
  rw [canonicalThetaProgram_cost, Nat.mul_comm (t0+c1) (c0+t1)]
  have := output_size_le (D := D) hc0 hc1 ht0 ht1 hh
  omega

omit [DecidableEq K] in
theorem theta_length_cap (v : LiftMatrices K D c0 c1 t0 t1 (liftBox D c1 t0 t1 c0 h)) :
    (canonicalThetaProgram v.psiHat v.phiHat).value.length ≤ 2*outputCap D s + 2*scalarCap s := by
  have hw := canonicalThetaProgram_length v.psiHat v.phiHat
  rw [Nat.mul_comm (t0+c1) (c0+t1)] at hw
  have ho := output_size_le (D := D) hc0 hc1 ht0 ht1 hh
  have hr := four_input_le_scalarCap s
  omega

omit [DecidableEq K] in
theorem theta_cost_polynomial (v : LiftMatrices K D c0 c1 t0 t1 (liftBox D c1 t0 t1 c0 h)) :
    (canonicalThetaProgram v.psiHat v.phiHat).cost ≤ (polynomial D).eval s := by
  rw [polynomial_eval]
  have := theta_cost_cap hc0 hc1 ht0 ht1 hh v
  unfold bound
  omega

omit [DecidableEq K] in
theorem theta_length_polynomial (v : LiftMatrices K D c0 c1 t0 t1 (liftBox D c1 t0 t1 c0 h)) :
    (canonicalThetaProgram v.psiHat v.phiHat).value.length ≤ (polynomial D).eval s := by
  rw [polynomial_eval]
  have := theta_length_cap hc0 hc1 ht0 ht1 hh v
  unfold bound
  omega

/-- One execution of the lift followed by one execution of the physical
compiler. The returned word is the actual canonical SUM/SWAP word. -/
theorem lift_and_theta_cost_polynomial :
    (Work.bind (liftMatricesProgram dC dT F G hs) fun v =>
      canonicalThetaProgram v.psiHat v.phiHat).cost ≤ (polynomial D).eval s := by
  rw [Work.bind_cost, polynomial_eval]
  have h₁ := (liftMatricesProgram_cost dC dT F G hs).trans (liftMatricesCost_le hc0 hc1 ht0 ht1 hh)
  have h₂ := theta_cost_cap hc0 hc1 ht0 ht1 hh (liftMatricesProgram dC dT F G hs).value
  unfold bound
  omega

theorem lift_and_theta_length_polynomial :
    (Work.bind (liftMatricesProgram dC dT F G hs) fun v =>
      canonicalThetaProgram v.psiHat v.phiHat).value.length ≤ (polynomial D).eval s :=
  theta_length_polynomial hc0 hc1 ht0 ht1 hh _

variable {NC NT : Type*} [AddCommGroup NC] [Module (Laurent K D) NC]
  [AddCommGroup NT] [Module (Laurent K D) NT]
variable (piC : (Fin c1 → Laurent K D) →ₗ[Laurent K D] NC)
  (piT : (Fin t1 → Laurent K D) →ₗ[Laurent K D] NT)
  (exactC : LinearMap.range (matrixDenote dC).mulVecLin = LinearMap.ker piC)
  (exactT : LinearMap.range (matrixDenote dT).mulVecLin = LinearMap.ker piT)
  (beta : NT ≃ₗ[Laurent K D] NC)
  (hF : piC.comp (matrixDenote F).mulVecLin = beta.toLinearMap.comp piT)
  (hG : piT.comp (matrixDenote G).mulVecLin = beta.symm.toLinearMap.comp piC)

theorem fromPresentationsProgram_cost_polynomial :
    (fromPresentationsProgram dC dT F G piC piT exactC exactT beta hF hG).cost ≤ (polynomial D).eval s :=
  liftMatricesProgram_cost_polynomial dC dT F G _ hc0 hc1 ht0 ht1 hh

theorem presentations_and_theta_cost_polynomial :
    (Work.bind (fromPresentationsProgram dC dT F G piC piT exactC exactT beta hF hG) fun v =>
      canonicalThetaProgram v.psiHat v.phiHat).cost ≤ (polynomial D).eval s :=
  lift_and_theta_cost_polynomial dC dT F G _ hc0 hc1 ht0 ht1 hh

theorem presentations_and_theta_length_polynomial :
    (Work.bind (fromPresentationsProgram dC dT F G piC piT exactC exactT beta hF hG) fun v =>
      canonicalThetaProgram v.psiHat v.phiHat).value.length ≤ (polynomial D).eval s :=
  lift_and_theta_length_polynomial dC dT F G _ hc0 hc1 ht0 ht1 hh

end Decoupling.HighDim.AlgorithmTwoInvertibleGrowth
