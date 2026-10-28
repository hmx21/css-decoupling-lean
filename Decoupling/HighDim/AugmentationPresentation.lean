import Decoupling.HighDim.TrivialLayers
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# HD012: evaluating relations of an augmentation-trivial module

Source: Appendix C5, the cohomology line of Algorithm 2. This proves the
actual quotient presentation over the coefficient field from given genuine
generators and relations. Obtaining bounded generators algorithmically is
a separate obligation; no solver or degree bound is assumed here.
-/
namespace Decoupling.HighDim.AugmentationPresentation
open CategoryTheory Matrix TrivialLayers
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D g t : ℕ}

abbrev free (g : ℕ) := ModuleCat.of (Laurent K D) (Fin g → Laurent K D)

def evaluate (g : ℕ) : Layers.coefficients (free (K := K) (D := D) g) ⟶ ModuleCat.of K (Fin g → K) :=
  ModuleCat.ofHom (X := Layers.coefficients (free (K := K) (D := D) g))
    (Y := ModuleCat.of K (Fin g → K)) {
    toFun v i := augmentation (v i)
    map_add' v w := by funext i; exact map_add augmentation _ _
    map_smul' a v := by
      funext i
      change augmentation (constant a * v i) = a * augmentation (v i)
      rw [map_mul, augmentation_constant] }

def constants (g : ℕ) : ModuleCat.of K (Fin g → K) ⟶ Layers.coefficients (free (K := K) (D := D) g) :=
  ModuleCat.ofHom (X := ModuleCat.of K (Fin g → K))
    (Y := Layers.coefficients (free (K := K) (D := D) g)) {
    toFun v i := constant (D := D) (v i)
    map_add' v w := by funext i; exact map_add constant _ _
    map_smul' a v := by
      funext i
      change constant (a * v i) = constant a * constant (v i)
      exact map_mul constant _ _ }

@[simp] theorem evaluate_constants (v : Fin g → K) :
    evaluate (K := K) (D := D) g (constants g v) = v := by
  funext i
  exact augmentation_constant (K := K) (D := D) (v i)

variable (H : ModuleCat (Laurent K D)) (W : free (K := K) (D := D) g ⟶ H)

def presentation : ModuleCat.of K (Fin g → K) ⟶ Layers.coefficients H :=
  constants g ≫ (ModuleCat.restrictScalars constant).map W

/-- Augmentation action allows all Laurent coefficients in a generator
expression to be replaced by their true values at x_i=1. -/
theorem map_constants_evaluate (hH : AugmentationAction H) (v : free (K := K) (D := D) g) :
    W (constants g (evaluate g v)) = W v := by
  have hv : v = ∑ i : Fin g, v i • Pi.single i (1 : Laurent K D) := by
    funext j
    simp [Pi.single_apply]
  have he : constants g (evaluate g v) =
      ∑ i : Fin g, constant (D := D) (augmentation (v i)) • Pi.single i (1 : Laurent K D) := by
    funext j
    simp [constants, evaluate, Pi.single_apply]
  rw [he, map_sum]
  conv_rhs => rw [hv, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [W.hom.map_smul, W.hom.map_smul]
  exact (hH (v i) (W (Pi.single i 1))).symm

theorem presentation_surjective (hH : AugmentationAction H) (hW : Function.Surjective W) :
    Function.Surjective (presentation H W) := by
  intro z
  obtain ⟨v, rfl⟩ := hW z
  exact ⟨evaluate g v, map_constants_evaluate H W hH v⟩

theorem evaluate_mulVec (U : Matrix (Fin g) (Fin t) (Laurent K D)) (v : Fin t → Laurent K D) :
    evaluate (K := K) (D := D) g (U *ᵥ v) = U.map augmentation *ᵥ evaluate t v := by
  funext i
  simp [evaluate, Matrix.mulVec, dotProduct, map_sum, map_mul]

/-- Genuine Laurent relations evaluate to precisely the kernel of the
coefficient-field generator map, not just a subspace of that kernel. -/
theorem presentation_kernel (hH : AugmentationAction H)
    (U : Matrix (Fin g) (Fin t) (Laurent K D))
    (hU : U.mulVecLin.range = W.hom.ker) :
    (presentation H W).hom.ker = (U.map augmentation).mulVecLin.range := by
  ext v
  constructor
  · intro hv
    have hc : constants g v ∈ W.hom.ker := hv
    rw [← hU] at hc
    obtain ⟨u, hu⟩ := hc
    refine ⟨evaluate t u, ?_⟩
    have he := congrArg (evaluate (K := K) (D := D) g) hu
    change evaluate g (U *ᵥ u) = evaluate g (constants g v) at he
    rw [evaluate_mulVec, evaluate_constants] at he
    exact he
  · rintro ⟨u, rfl⟩
    have hc : U *ᵥ constants t u ∈ W.hom.ker := by
      rw [← hU]
      exact ⟨constants t u, rfl⟩
    have he := map_constants_evaluate H W hH (U *ᵥ constants t u)
    rw [evaluate_mulVec, evaluate_constants] at he
    exact he.trans hc

/-- The coefficient quotient in C5, constructed from actual generators,
relations and augmentation action. The evaluated columns span its denominator. -/
def coefficientPresentationEquiv (hH : AugmentationAction H) (hW : Function.Surjective W)
    (U : Matrix (Fin g) (Fin t) (Laurent K D))
    (hU : U.mulVecLin.range = W.hom.ker) :
    Layers.coefficients H ≃ₗ[K] (Fin g → K) ⧸ (U.map augmentation).mulVecLin.range :=
  ((presentation H W).hom.quotKerEquivOfSurjective (presentation_surjective H W hH hW)).symm.trans
    (Submodule.quotEquivOfEq _ _ (presentation_kernel H W hH U hU))

theorem coefficientPresentationEquiv_apply (hH : AugmentationAction H)
    (hW : Function.Surjective W) (U : Matrix (Fin g) (Fin t) (Laurent K D))
    (hU : U.mulVecLin.range = W.hom.ker) (v : Fin g → K) :
    coefficientPresentationEquiv H W hH hW U hU (presentation H W v) =
      (U.map augmentation).mulVecLin.range.mkQ v := by
  change Submodule.quotEquivOfEq _ _ (presentation_kernel H W hH U hU)
    (((presentation H W).hom.quotKerEquivOfSurjective
      (presentation_surjective H W hH hW)).symm ((presentation H W).hom v)) = _
  rw [LinearMap.quotKerEquivOfSurjective_symm_apply]
  rfl

end
end Decoupling.HighDim.AugmentationPresentation
