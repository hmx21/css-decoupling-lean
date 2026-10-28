import Decoupling.HighDim.TorusSplitCount

/-! The actual endpoint morphism spaces used by the example's rank losses. -/

namespace Decoupling.HighDim.GluedRankLoss

open CategoryTheory CategoryTheory.Abelian Koszul Torus
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (D : ℕ)

/-- An endomorphism of the genuine augmentation module is determined by
its value at 1, with its true coefficient-field linear structure. -/
def coefficientEndValues : Layers.coefficients (ModuleCat.of (Laurent K D)
    (coefficientModule K D ⟶ coefficientModule K D)) ≃ₗ[K] K where
  toFun f := (show coefficientModule K D ⟶ coefficientModule K D from f) (1 : K)
  invFun b := ModuleCat.ofHom (X := coefficientModule K D) (Y := coefficientModule K D) {
    toFun x := (show K from x) * b
    map_add' x y := by
      change ((show K from x) + (show K from y)) * b = _
      exact add_mul (show K from x) (show K from y) b
    map_smul' r x := by
      change (augmentation r * (show K from x)) * b = augmentation r * ((show K from x) * b)
      ring }
  left_inv f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    have h := (show coefficientModule K D ⟶ coefficientModule K D from f).hom.map_smul
      (constant (D := D) (show K from x)) (1 : K)
    change (show coefficientModule K D ⟶ coefficientModule K D from f)
      (augmentation (constant (D := D) (show K from x)) * 1) =
        augmentation (constant (D := D) (show K from x)) *
          (show K from (show coefficientModule K D ⟶ coefficientModule K D from f) (1 : K)) at h
    simpa using h.symm
  right_inv b := one_mul b
  map_add' _ _ := rfl
  map_smul' a f := by
    change augmentation (constant (D := D) a) *
      (show K from (show coefficientModule K D ⟶ coefficientModule K D from f) (1 : K)) = _
    simp

def extZeroCoefficientEquiv : Layers.coefficients (ModuleCat.of (Laurent K D)
    (Ext (coefficientModule K D) (coefficientModule K D) 0)) ≃ₗ[K]
      Layers.coefficients (ModuleCat.of (Laurent K D)
        (coefficientModule K D ⟶ coefficientModule K D)) where
  toFun := Ext.linearEquiv₀ (R := Laurent K D)
  invFun := (Ext.linearEquiv₀ (R := Laurent K D)).symm
  left_inv := (Ext.linearEquiv₀ (R := Laurent K D)).symm_apply_apply
  right_inv := (Ext.linearEquiv₀ (R := Laurent K D)).apply_symm_apply
  map_add' := (Ext.linearEquiv₀ (R := Laurent K D)).map_add
  map_smul' a f := (Ext.linearEquiv₀ (R := Laurent K D)).map_smul (constant (D := D) a) f

def probeEndEquiv : homCoefficients (probe K D) (probe K D) ≃ₗ[K] K :=
  (probeSingleExtEquiv (coefficientModule K D) D 0 (by simp)).trans
    ((extZeroCoefficientEquiv K D).trans (coefficientEndValues K D))

instance probeEnd_finite : Module.Finite K (homCoefficients (probe K D) (probe K D)) :=
  Module.Finite.equiv (probeEndEquiv K D).symm

theorem probeEnd_finrank : Module.finrank K (homCoefficients (probe K D) (probe K D)) = 1 :=
  (probeEndEquiv K D).finrank_eq.trans (Module.finrank_self K)

/-- All positive coefficient Ext ranks, including the top degree. The
trivial-action premise is proved for this actual coefficient module. -/
theorem coefficientExt_finrank (n : ℕ) :
    Module.finrank K (Layers.coefficients (ModuleCat.of (Laurent K D)
      (Ext (coefficientModule K D) (coefficientModule K D) (n + 1)))) =
        D.choose (n + 1) := by
  have hz : (layerSc (coefficientModule K D) n).f = 0 ∧
      (layerSc (coefficientModule K D) n).g = 0 := by
    constructor
    · ext f
      rw [layerSc_f_apply]
      exact dual_boundary_zero_of_augmentation _ TrivialLayers.augmentationAction_coefficientModule n f
    · ext f
      rw [layerSc_g_apply]
      exact dual_boundary_zero_of_augmentation _ TrivialLayers.augmentationAction_coefficientModule (n + 1) f
  rw [← (layerHomologyEquivExt (coefficientModule K D) n).finrank_eq,
    (finrank_homology_eq_iff _).mpr hz, layerSc_finrank, coefficientModule_finrank, mul_one]

theorem probeBottom_finrank : Module.finrank K (homCoefficients (probe K 3)
    ((DerivedCategory.singleFunctor (ModuleCat (Laurent K 3)) 0).obj (coefficientModule K 3))) = 1 := by
  exact (probeSingleExtEquiv (coefficientModule K 3) 0 3 (by decide)).finrank_eq.trans
    (coefficientExt_finrank K 3 2)

end
end Decoupling.HighDim.GluedRankLoss
