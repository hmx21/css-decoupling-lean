import Decoupling.HighDim.CohomologyRelations
import Decoupling.HighDim.FiniteLinearSolverQuotient

/-!
# HD012 the computed quotient basis is a basis of actual native cohomology

Given the true kernel and relation matrices, the Gaussian free-row indices
select actual columns of W as cocycles. The proof identifies their classes
with a native basis of homology. There is no arbitrary basis choice for the
cohomology module in this construction.
-/
namespace Decoupling.HighDim.CohomologyPresentation
open Matrix CategoryTheory
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D m q r g t : ℕ}
  (b : Matrix (Fin q) (Fin m) (Laurent K D))
  (d : Matrix (Fin r) (Fin q) (Laurent K D)) (hbd : d * b = 0)
  (W : Matrix (Fin q) (Fin g) (Laurent K D))
  (hW : W.mulVecLin.range = d.mulVecLin.ker)
  (hH : TrivialLayers.AugmentationAction (window b d hbd).homology)
  (U : Matrix (Fin g) (Fin t) (Laurent K D))
  (hU : U.mulVecLin.range = relations b W)
  (U₀ : FiniteLinearSolver.DenseMatrix K g t)
  (hU₀ : U.map augmentation = FiniteLinearSolver.matrix U₀)

def computedCoordinates :
    Layers.coefficients (window b d hbd).homology ≃ₗ[K]
      (Fin (FiniteLinearSolver.quotientData U₀).value.dimension → K) :=
  (cohomologyEquiv b d hbd W hW hH U hU).trans
    ((Submodule.quotEquivOfEq _ _ (congrArg
      (fun A : Matrix (Fin g) (Fin t) K => A.mulVecLin.range) hU₀)).trans
      (FiniteLinearSolver.quotientEquiv U₀))

def computedCocycle (j : Fin (FiniteLinearSolver.quotientData U₀).value.dimension) :
    Fin q → Laurent K D :=
  W.col (FiniteLinearSolver.quotientData U₀).value.freeColumns[j]

include hW in
theorem computedCocycle_closed (j : Fin (FiniteLinearSolver.quotientData U₀).value.dimension) :
    d *ᵥ computedCocycle W U₀ j = 0 := by
  have hm : W *ᵥ Pi.single (FiniteLinearSolver.quotientData U₀).value.freeColumns[j] 1
      ∈ d.mulVecLin.ker := by
    rw [← hW]
    exact ⟨_, rfl⟩
  simp only [Matrix.mulVec_single_one] at hm
  exact hm

def computedClass (j : Fin (FiniteLinearSolver.quotientData U₀).value.dimension) :
    Layers.coefficients (window b d hbd).homology :=
  Glued.cycleClass (window b d hbd) (computedCocycle W U₀ j) (computedCocycle_closed d W hW U₀ j)

theorem computedCoordinates_class (j : Fin (FiniteLinearSolver.quotientData U₀).value.dimension) :
    computedCoordinates b d hbd W hW hH U hU U₀ hU₀ (computedClass b d hbd W hW U₀ j) =
      Pi.single j 1 := by
  let v := FiniteLinearSolver.quotientRepresentative U₀ j
  have hv : computedClass b d hbd W hW U₀ j =
      AugmentationPresentation.presentation _ (generators b d hbd W hW) v := by
    have hc : AugmentationPresentation.constants (K := K) (D := D) g v =
        Pi.single (FiniteLinearSolver.quotientData U₀).value.freeColumns[j] 1 := by
      funext i
      change constant (D := D) (v i) =
        (Pi.single (FiniteLinearSolver.quotientData U₀).value.freeColumns[j]
          (1 : Laurent K D) : Fin g → Laurent K D) i
      dsimp only [v, FiniteLinearSolver.quotientRepresentative]
      by_cases hi : i = (FiniteLinearSolver.quotientData U₀).value.freeColumns[j]
      · subst i
        simp only [Pi.single_eq_same]
        exact map_one constant
      · rw [Pi.single_eq_of_ne hi, Pi.single_eq_of_ne hi]
        exact map_zero constant
    change Glued.cycleClass (window b d hbd) (computedCocycle W U₀ j) _ =
      generators b d hbd W hW (AugmentationPresentation.constants g v)
    rw [hc, generators_apply]
    apply (ModuleCat.mono_iff_injective (window b d hbd).homologyι).mp inferInstance
    rw [Glued.cycleClass_ι, Glued.cycleClass_ι]
    apply congrArg (window b d hbd).pOpcycles
    exact (Matrix.mulVec_single_one _ _).symm
  rw [hv]
  change FiniteLinearSolver.quotientEquiv U₀ (Submodule.quotEquivOfEq _ _ _
    (AugmentationPresentation.coefficientPresentationEquiv _ (generators b d hbd W hW)
      hH _ U _ (AugmentationPresentation.presentation _ _ v))) = _
  rw [AugmentationPresentation.coefficientPresentationEquiv_apply]
  exact FiniteLinearSolver.quotientEquiv_representative U₀ j

def computedBasis :
    Module.Basis (Fin (FiniteLinearSolver.quotientData U₀).value.dimension) K
      (Layers.coefficients (window b d hbd).homology) :=
  (Pi.basisFun K _).map (computedCoordinates b d hbd W hW hH U hU U₀ hU₀).symm

theorem computedBasis_apply (j : Fin (FiniteLinearSolver.quotientData U₀).value.dimension) :
    computedBasis b d hbd W hW hH U hU U₀ hU₀ j = computedClass b d hbd W hW U₀ j := by
  apply (computedCoordinates b d hbd W hW hH U hU U₀ hU₀).injective
  rw [computedCoordinates_class]
  change (computedCoordinates b d hbd W hW hH U hU U₀ hU₀)
    ((computedCoordinates b d hbd W hW hH U hU U₀ hU₀).symm (Pi.basisFun K _ j)) = _
  rw [LinearEquiv.apply_symm_apply, Pi.basisFun_apply]

include hW hH hU hU₀ in
theorem computed_dimension :
    Module.finrank K (Layers.coefficients (window b d hbd).homology) =
      (FiniteLinearSolver.quotientData U₀).value.dimension := by
  rw [(computedCoordinates b d hbd W hW hH U hU U₀ hU₀).finrank_eq, Module.finrank_fin_fun]

end
end Decoupling.HighDim.CohomologyPresentation
