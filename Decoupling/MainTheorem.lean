import Decoupling.SwanInduction
import Decoupling.FreeResolutionBound
import Decoupling.FinalDecoupling

/-!
# Decoupling from precisely the manuscript's assumptions

The Laurent finite-projective freeness input is now a proved theorem. The
statements here supply the finite-free resolution and the entire decoupling
certificate from the original topological and finite-Ext-layer assumptions.
-/

namespace Decoupling.MainTheorem

open ResolutionExt LayerTranslations

noncomputable section

variable {q s r : ℕ} (c : CSS.Checks q s r)

theorem laurent_freeness (M : ModuleCat.{0} R)
    (hfin : Module.Finite R M) (hproj : Module.Projective R M) : Module.Free R M := by
  let := hfin
  let := hproj
  exact SwanInduction.paperRing_free M

/-- Lemma I.1, including existence of the actual supplied-prefix resolution. -/
theorem exists_free_resolution (hTop : c.Topological) :
    ∃ cX : ℕ, Nonempty (CSSResolution c cX) :=
  FreeResolutionBound.exists_free_resolution_of_freeness c hTop laurent_freeness

/-- Complete stable decoupling, with no additional algebraic theorem,
splitting, comparison map, retained period, or circuit supplied as input. -/
theorem decoupling (hTop : c.Topological)
    [FiniteDimensional (ZMod 2) (coefficients (layer c 1))]
    [FiniteDimensional (ZMod 2) (coefficients (layer c 2))] :
    ∃ cX : ℕ, ∃ n : ℕ+, Nonempty (FinalDecoupling.Result c cX n) :=
  FinalDecoupling.exists_result_of_laurent_freeness c hTop laurent_freeness

/-- Selects an actual certificate. This construction uses classical choice;
its algebraic and circuit correctness is supplied by `decoupling`. -/
def certificate (hTop : c.Topological)
    [FiniteDimensional (ZMod 2) (coefficients (layer c 1))]
    [FiniteDimensional (ZMod 2) (coefficients (layer c 2))] :
    Σ cX : ℕ, Σ n : ℕ+, FinalDecoupling.Result c cX n := by
  let cX := Classical.choose (decoupling c hTop)
  let hn := Classical.choose_spec (decoupling c hTop)
  exact ⟨cX, Classical.choose hn, Classical.choice (Classical.choose_spec hn)⟩

end
end Decoupling.MainTheorem
