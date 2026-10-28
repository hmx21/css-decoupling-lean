import Decoupling.HighDim.AugmentationPresentation
import Decoupling.HighDim.GluedNativeHomology

/-!
# HD012 Algorithm 2: the actual cohomology quotient from kernel generators

The generator and relation hypotheses below are exact matrix range/kernel
identities, to be supplied by verified linear-system routines. The resulting
field quotient is proved isomorphic to native homology. No cohomology
dimension, basis, or solver correctness is built into its definition.
-/
namespace Decoupling.HighDim.CohomologyPresentation
open CategoryTheory CategoryTheory.Limits Matrix
open AugmentationPresentation
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D m q r g t : ℕ}
  (b : Matrix (Fin q) (Fin m) (Laurent K D))
  (d : Matrix (Fin r) (Fin q) (Laurent K D)) (hbd : d * b = 0)

def window : ShortComplex (ModuleCat (Laurent K D)) :=
  ShortComplex.moduleCatMk b.mulVecLin d.mulVecLin (by
    apply LinearMap.ext
    intro v
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply,
      Matrix.mulVec_mulVec, hbd, Matrix.zero_mulVec, LinearMap.zero_apply])

variable (W : Matrix (Fin q) (Fin g) (Laurent K D)) (hW : W.mulVecLin.range = d.mulVecLin.ker)

def generators : AugmentationPresentation.free (K := K) (D := D) g ⟶ (window b d hbd).homology :=
  ModuleCat.ofHom (W.mulVecLin.codRestrict d.mulVecLin.ker (fun v => by
    rw [← hW]
    exact ⟨v, rfl⟩)) ≫ (window b d hbd).moduleCatCyclesIso.inv ≫ (window b d hbd).homologyπ

theorem generators_apply (v : Fin g → Laurent K D) :
    generators b d hbd W hW v = Glued.cycleClass (window b d hbd) (W *ᵥ v)
      (by change d.mulVecLin (W.mulVecLin v) = 0
          have hm : W.mulVecLin v ∈ d.mulVecLin.ker := by rw [← hW]; exact ⟨v, rfl⟩
          exact hm) := rfl

theorem generators_surjective : Function.Surjective (generators b d hbd W hW) := by
  intro z
  obtain ⟨v, hv, rfl⟩ := Glued.cycleClass_surjective (window b d hbd) z
  have hm : v ∈ W.mulVecLin.range := by
    rw [hW]
    exact hv
  obtain ⟨u, rfl⟩ := hm
  exact ⟨u, rfl⟩

/-- The relations are exactly those combinations of W that are actual boundaries. -/
def relations : Submodule (Laurent K D) (Fin g → Laurent K D) :=
  b.mulVecLin.range.comap W.mulVecLin

theorem generators_kernel : (generators b d hbd W hW).hom.ker = relations b W := by
  ext u
  change Glued.cycleClass (window b d hbd) (W *ᵥ u) _ = 0 ↔
    ∃ v : Fin m → Laurent K D, b *ᵥ v = W *ᵥ u
  exact Glued.cycleClass_eq_zero_iff (window b d hbd) _ _

/-- The precise native cohomology quotient used in Appendix C5. -/
def cohomologyEquiv
    (hH : TrivialLayers.AugmentationAction (window b d hbd).homology)
    (U : Matrix (Fin g) (Fin t) (Laurent K D)) (hU : U.mulVecLin.range = relations b W) :
    Layers.coefficients (window b d hbd).homology ≃ₗ[K]
      (Fin g → K) ⧸ (U.map augmentation).mulVecLin.range :=
  coefficientPresentationEquiv _ (generators b d hbd W hW) hH
    (generators_surjective b d hbd W hW) U (hU.trans (generators_kernel b d hbd W hW).symm)

end
end Decoupling.HighDim.CohomologyPresentation
