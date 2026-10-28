import Decoupling.HighDim.SchreyerLocalizationExistence
import Decoupling.HighDim.SchreyerCSSPresentation

/-!
# HD014 closing the actual CSS Schreyer-tail inputs

The two tails are constructed from the actual Laurent kernels. No free
resolution, terminal basis or Gröbner certificate remains an input. A
prescribed third matrix can be retained; when it is not supplied its
finite generators are derived from the original X-check kernel.
-/
namespace Decoupling.HighDim.SchreyerCSS
open CategoryTheory SchreyerLocalization
noncomputable section
variable {K : Type} [Field K] {D q s r : ℕ}

def inputOfGamma (c : CSS.Checks K D q s r) {t : ℕ}
    (gamma : Matrix (Fin t) (Fin s) (Laurent K D))
    (hgamma : LinearMap.range (dagger gamma).mulVecLin =
      LinearMap.ker (dagger c.H_X).mulVecLin) : Input c where
  t := t
  gamma := gamma
  exact_gamma := hgamma
  positive := submoduleData (LinearMap.ker (dagger gamma).mulVecLin)
  negative := submoduleData (LinearMap.ker (FiniteResolution.zCover c).hom)

@[simp] theorem inputOfGamma_gamma (c : CSS.Checks K D q s r) {t : ℕ}
    (gamma : Matrix (Fin t) (Fin s) (Laurent K D))
    (hgamma : LinearMap.range (dagger gamma).mulVecLin =
      LinearMap.ker (dagger c.H_X).mulVecLin) : (inputOfGamma c gamma hgamma).gamma=gamma := rfl

theorem exists_input (c : CSS.Checks K D q s r) : Nonempty (Input c) := by
  obtain ⟨t,gamma,hgamma⟩ := exists_gamma c
  exact ⟨inputOfGamma c gamma hgamma⟩

def input (c : CSS.Checks K D q s r) : Input c := Classical.choice (exists_input c)

end
end Decoupling.HighDim.SchreyerCSS
