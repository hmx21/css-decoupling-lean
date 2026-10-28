import Decoupling.ExplicitFinal
import Decoupling.MainTheorem

/-!
# The complete manuscript construction from its original assumptions

The internally proved Laurent-projective freeness theorem supplies the actual
finite-free relation resolution.  The final result contains the original Ext
multiplicities, retained period, explicit Appendix C representative matrices,
the selected literal comparison `φ₀=(T,V+T C V(1))`, both stabilized image
equalities, and a finite physical CNOT circuit.  Neither Swan freeness nor a
resolution, splitting, comparison, or circuit is an additional hypothesis.

The construction is an algebraic existence proof using classical choice; it
does not claim a terminating executable algorithm for Laurent-system solves.
-/

namespace Decoupling.ExplicitMain

open LayerTranslations ResolutionExt

noncomputable section

variable {q s r : ℕ} (c : CSS.Checks q s r)

/-- Full decoupling with all selected manuscript matrices, under only the
original topological and finite genuine Ext-layer assumptions. -/
theorem decoupling (hTop : c.Topological)
    [FiniteDimensional (ZMod 2) (coefficients (layer c 1))]
    [FiniteDimensional (ZMod 2) (coefficients (layer c 2))] :
    ∃ cX : ℕ, ∃ h : CSSResolution c cX, ∃ n : ℕ+,
      Nonempty (ExplicitFinal.Result c h n) :=
  ExplicitFinal.exists_result_of_laurent_freeness c hTop MainTheorem.laurent_freeness

/-- The complete selected output: resolution and period are outputs too. -/
structure Output where
  coverRank : ℕ
  resolution : CSSResolution c coverRank
  period : ℕ+
  result : ExplicitFinal.Result c resolution period

theorem exists_output (hTop : c.Topological)
    [FiniteDimensional (ZMod 2) (coefficients (layer c 1))]
    [FiniteDimensional (ZMod 2) (coefficients (layer c 2))] : Nonempty (Output c) := by
  obtain ⟨cX, h, n, ⟨out⟩⟩ := decoupling c hTop
  exact ⟨⟨cX, h, n, out⟩⟩

/-- A chosen physical/algebraic certificate with the same exact correctness
guarantees as `decoupling`, including all empty-layer cases. -/
def construct (hTop : c.Topological)
    [FiniteDimensional (ZMod 2) (coefficients (layer c 1))]
    [FiniteDimensional (ZMod 2) (coefficients (layer c 2))] : Output c :=
  Classical.choice (exists_output c hTop)

end
end Decoupling.ExplicitMain
