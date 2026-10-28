import Decoupling.HighDim.PiResolutionDual

/-!
# Full native profiles of finite products of reduced modules

This is a derived-object statement, obtained from an actual product
resolution and its actual Hom complex. It does not infer splitting from
the dimensions of Ext groups.
-/

namespace Decoupling.HighDim.ProfileStability

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
noncomputable section
attribute [local instance] Classical.propDecidable HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [CommRing K] {D : ℕ} {ι : Type} [Fintype ι]
  (M : ι → ModuleCat (Laurent K D))

def conjugatePiEquiv :
    Layers.conjugate (ModuleCat.of (Laurent K D) (∀ i, M i)) ≃ₗ[Laurent K D]
      (∀ i, Layers.conjugate (M i)) where
  toFun x i := x i
  invFun x i := x i
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- A finite direct product of reduced modules gives the corresponding
finite biproduct of complete positive derived profiles. -/
def modulePiProfileIso :
    moduleProfile (ModuleCat.of (Laurent K D) (∀ i, M i)) ≅
      ⨁ fun i => moduleProfile (M i) := by
  let P := fun i => projectiveResolution (Layers.conjugate (M i))
  let Y := ModuleCat.of (Laurent K D) (Laurent K D)
  exact (ResolutionComparison.profileIsoOfModuleIso Y (PiResolution.resolution P)
    (conjugatePiEquiv M).symm.toModuleIso
    (projectiveResolution (Layers.conjugate
      (ModuleCat.of (Laurent K D) (∀ i, M i))))).symm ≪≫
    PiResolution.profileBiproductIso P Y

end
end Decoupling.HighDim.ProfileStability
