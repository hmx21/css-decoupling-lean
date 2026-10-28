import Decoupling.HighDim.AlgorithmTwoComparisonStackAugmentation
import Decoupling.HighDim.AlgorithmTwoComparisonZeroLift
import Decoupling.HighDim.AlgorithmTwoComparisonCone

/-!
# Solvability of Algorithm 2's prescribed comparison and contraction

The supplied complex is derived-isomorphic to the actual toric stack.
The remaining inputs are the chosen native cohomology coordinates and
their representing cocycles. The actual comparison and its actual
cone contraction are constructed as mathematical witnesses; no such
map, homotopy, or solution is assumed.
-/
namespace Decoupling.HighDim.AlgorithmTwoComparison
open CategoryTheory HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
attribute [local instance] HasDerivedCategory.standard
variable (K : Type) [Field K] (D : ℕ) {ι : Type} [Fintype ι] (forms : ι → ℕ)
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (e : DerivedCategory.Q.obj (Toric.stackModel K D forms) ≅ DerivedCategory.Q.obj C)
  (b : ∀ n, (stackZeroModel K D forms).X n ≅ C.homology n)
  (c : ∀ i, C.X (forms i + 1))
  (hc : ∀ i, C.d (forms i + 1) (((forms i : ℤ) + 1) + 1) (c i) = 0)
  (hclass : ∀ i, nativeCycleClass C (forms i + 1) (c i) (hc i) =
    (b (forms i + 1)).hom (stackTopImage K D forms i))

include e b hc hclass

/-- Actual prescribed empty-cell values and quasi-isomorphism, with no
comparison-map existence premise. -/
theorem exists_prescribed_comparison :
    ∃ g : Toric.stackModel K D forms ⟶ C, QuasiIso g ∧
      ∀ i, g.f (forms i + 1) (stackTop K D forms i) = c i := by
  let : (Toric.stackModel K D forms).IsKProjective :=
    CochainComplex.isKProjective_of_projective _ (Toric.stackBound forms)
  obtain ⟨f, hf, hQ, hH⟩ := exists_zeroComparison (stackZeroModel_d K D forms)
    (stackAugmentation K D forms) e b
  let : QuasiIso f := hf
  have heq : ∀ i, nativeCycleClass C (forms i + 1) (c i) (hc i) =
      nativeCycleClass C (forms i + 1) (f.f (forms i + 1) (stackTop K D forms i)) (by
        change (f.f (forms i + 1) ≫ C.d _ _) (stackTop K D forms i) = 0
        rw [f.comm]
        change f.f _ ((Toric.stackModel K D forms).d _ _ (stackTop K D forms i)) = 0
        rw [stackTop_closed, map_zero]) := by
    intro i
    rw [hclass, ← nativeCycleClass_naturality f _ _ (stackTop_closed K D forms i),
      hH (forms i + 1) (stackTop K D forms i) (stackTop_closed K D forms i)]
    rfl
  obtain ⟨g, hg, _, htop⟩ := exists_stack_prescribed K D forms f c hc heq
  exact ⟨g, hg, htop⟩

/-- Both native linear systems in Algorithm 2's comparison line are
solvable: prescribed Γ and the contraction of its genuine cone. -/
theorem exists_prescribed_comparison_and_contraction
    (cC : StableFree.Coordinates C) (upperC : ℤ) [C.IsStrictlyLE upperC] :
    ∃ g : Toric.stackModel K D forms ⟶ C, QuasiIso g ∧
      (∀ i, g.f (forms i + 1) (stackTop K D forms i) = c i) ∧
      Nonempty (Homotopy (𝟙 (CochainComplex.mappingCone g)) 0) := by
  obtain ⟨g, hg, htop⟩ := exists_prescribed_comparison K D forms e b c hc hclass
  let : QuasiIso g := hg
  exact ⟨g, hg, htop, ⟨coneContraction g (StableFree.Coordinates.ofFiniteFree _)
    cC (Toric.stackBound forms) upperC⟩⟩

end
end Decoupling.HighDim.AlgorithmTwoComparison
