import Decoupling.HighDim.AlgorithmTwoCohomologyData

/-!
# HD012 correctness of the actual cohomology program

The final theorem assumes only the differential equation and the actual
augmentation action on the native homology of the input window. The
kernel and relation-generator contracts are discharged by the executable
Laurent routines; no presentation or cohomology basis is supplied.
Augmentation action is the consequence of Algorithm 2's split-profile input,
to be connected at the full-complex entry point.
-/
namespace Decoupling.HighDim.AlgorithmTwoCohomology
open Matrix ArithmeticCost
open LaurentArithmetic CohomologyPresentation
noncomputable section
variable {K : Type} [Field K] [DecidableEq K] {D q m r h B B' g t : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def Result.cycle (o : Result K D q B) (j : Fin o.dimension) : Fin q → Laurent K D :=
  (matrixDenote o.cocycles).col j

structure Correct (b : Matrix (Fin q) (Fin m) (Laurent K D))
    (d : Matrix (Fin r) (Fin q) (Laurent K D)) (hbd : d * b = 0)
    (o : Result K D q B) : Prop where
  closed : ∀ j, d *ᵥ o.cycle j = 0
  basis : ∃ e : Module.Basis (Fin o.dimension) K (Layers.coefficients (window b d hbd).homology),
    ∀ j, e j = Glued.cycleClass (window b d hbd) (o.cycle j) (closed j)

theorem finish_correct (b : DenseMatrix K D q m h) (d : DenseMatrix K D r q h)
    (hbd : matrixDenote d * matrixDenote b = 0)
    (hH : TrivialLayers.AugmentationAction (window (matrixDenote b) (matrixDenote d) hbd).homology)
    (W : DenseMatrix K D q g B) (V : DenseMatrix K D (g + m) t B')
    (hW : (matrixDenote W).mulVecLin.range = (matrixDenote d).mulVecLin.ker)
    (hV : (matrixDenote V).mulVecLin.range =
      (indexedRelationSystem (matrixDenote b) (matrixDenote W)).mulVecLin.ker) :
    Correct (matrixDenote b) (matrixDenote d) hbd (finish W V).value := by
  let U := matrixDenote (projectRelations V)
  let U₀ := (matrixAugmentationProgram (projectRelations V)).value
  have hU : U.mulVecLin.range = relations (matrixDenote b) (matrixDenote W) := by
    rw [show U = indexedRelationProjection (matrixDenote V) from projectRelations_denote V]
    exact indexedRelationProjection_range (matrixDenote b) (matrixDenote W) (matrixDenote V) hV
  have hU₀ : U.map augmentation = FiniteLinearSolver.matrix U₀ :=
    (matrixAugmentationProgram_correct (projectRelations V)).symm
  have hc (j : Fin (finish W V).value.dimension) :
      (finish W V).value.cycle j = computedCocycle (matrixDenote W) U₀ j := by
    change (matrixDenote (selectCocycles W (FiniteLinearSolver.quotientData U₀).value.freeColumns)).col j = _
    rw [selectCocycles_denote]
    rfl
  have hclosed : ∀ j, matrixDenote d *ᵥ (finish W V).value.cycle j = 0 := by
    intro j
    rw [hc]
    exact computedCocycle_closed (matrixDenote d) (matrixDenote W) hW U₀ j
  refine ⟨hclosed, ⟨computedBasis (matrixDenote b) (matrixDenote d) hbd
    (matrixDenote W) hW hH U hU U₀ hU₀, ?_⟩⟩
  intro j
  refine (computedBasis_apply (matrixDenote b) (matrixDenote d) hbd
    (matrixDenote W) hW hH U hU U₀ hU₀ j).trans ?_
  change Glued.cycleClass (window (matrixDenote b) (matrixDenote d) hbd)
    (computedCocycle (matrixDenote W) U₀ j) _ = _
  apply (ModuleCat.mono_iff_injective (window (matrixDenote b) (matrixDenote d) hbd).homologyι).mp
    inferInstance
  rw [Glued.cycleClass_ι, Glued.cycleClass_ι]
  exact congrArg (window (matrixDenote b) (matrixDenote d) hbd).pOpcycles (hc j).symm

/-- All intermediate kernel/presentation hypotheses are discharged from
the actual program. Empty cohomology and empty check spaces are included. -/
theorem compute_correct (b : DenseMatrix K D q m h) (d : DenseMatrix K D r q h)
    (hbd : matrixDenote d * matrixDenote b = 0)
    (hH : TrivialLayers.AugmentationAction (window (matrixDenote b) (matrixDenote d) hbd).homology) :
    Correct (matrixDenote b) (matrixDenote d) hbd (compute b d).value := by
  let W := (LaurentLinearSolver.kernel d).value
  let R := (relationInput b W.coefficients).value
  let V := (LaurentLinearSolver.kernel R).value
  have hW := LaurentLinearSolver.kernel_correct d
  have hV : (matrixDenote V.coefficients).mulVecLin.range =
      (indexedRelationSystem (matrixDenote b) (matrixDenote W.coefficients)).mulVecLin.ker := by
    have he := LaurentLinearSolver.kernel_correct R
    rw [show matrixDenote R = indexedRelationSystem (matrixDenote b) (matrixDenote W.coefficients)
      from relationInput_denote b W.coefficients] at he
    exact he
  exact finish_correct b d hbd hH W.coefficients V.coefficients hW hV

omit [DecidableEq K] in
theorem Correct.dimension_eq {b : Matrix (Fin q) (Fin m) (Laurent K D)}
    {d : Matrix (Fin r) (Fin q) (Laurent K D)} {hbd : d * b = 0}
    {o : Result K D q B} (ho : Correct b d hbd o) :
    Module.finrank K (Layers.coefficients (window b d hbd).homology) = o.dimension := by
  obtain ⟨e, _⟩ := ho.basis
  exact (Module.finrank_eq_card_basis e).trans (Fintype.card_fin _)

end
end Decoupling.HighDim.AlgorithmTwoCohomology
