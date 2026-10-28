import Decoupling.FreeResolution
import Decoupling.LaurentGlobalDimension

/-!
# The remaining freeness input for the CSS free-resolution lemma

The Laurent global projective-dimension bound has been proved. Consequently
the relation kernel below is now unconditionally finite and projective.
Only its freeness is left as a separate input to the free-resolution result.
-/

namespace Decoupling.FreeResolutionBound

open CategoryTheory

noncomputable section

variable {q s t : ℕ} (c : CSS.Checks q s t) (hc : c.Topological)

include hc

/-- The actual reduced module has projective dimension at most two. -/
theorem reduced_projectiveDimensionLE_two :
    HasProjectiveDimensionLE (ModuleCat.of R c.M_X) 2 :=
  FreeResolution.reduced_projectiveDimensionLE_two c hc
    (LaurentGlobalDimension.laurent_global_bound _)

/-- Topological exactness implies projectivity of the actual second
relation kernel; no global homological-dimension premise remains. -/
theorem relationKernel_projective :
    Module.Projective R (FreeResolution.RelationKernel c) :=
  FreeResolution.relationKernel_projective c (reduced_projectiveDimensionLE_two c hc)

/-- The exact remaining mathematical condition for the free resolution is
freeness of finite projective modules over the actual Laurent ring. -/
theorem exists_free_resolution_of_freeness
    (hfreeness : ∀ M : ModuleCat.{0} R,
      Module.Finite R M → Module.Projective R M → Module.Free R M) :
    ∃ cX, Nonempty (ResolutionExt.CSSResolution c cX) :=
  FreeResolution.exists_free_resolution_of_global_bound_and_freeness c hc
    LaurentGlobalDimension.laurent_global_bound hfreeness

end

end Decoupling.FreeResolutionBound
