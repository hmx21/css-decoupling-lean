import Decoupling.HighDim.KoszulLatticeExt

/-!
# Arbitrary-lattice restriction of finite-source native Ext

Source: Proposition `prop:superlattice`, Appendix B.2. All coordinate
splittings below are those of the original source module, and restriction
is the real scalar-restriction exact functor.
-/

namespace Decoupling.HighDim.KoszulLattice

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.Preadditive
open Koszul ExtValues TrivialLayers
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ}

theorem finite_restriction_eq_zero_iff_coordinates (a : Translation D →+ Translation D)
    (B A : ModuleCat (Laurent K D)) [FiniteDimensional K (Layers.coefficients B)]
    (hB : AugmentationAction B) (n : ℕ) (e : Ext B A n) :
    e.mapExactFunctor (ModuleCat.restrictScalars (latticeMap K a)) = 0 ↔
      ∀ i : Fin (Module.finrank K (Layers.coefficients B)),
        ((Ext.mk₀ (sourceInclusion B hB i)).comp e (zero_add n)).mapExactFunctor
          (ModuleCat.restrictScalars (latticeMap K a)) = 0 := by
  let F := ModuleCat.restrictScalars (latticeMap K a)
  constructor
  · intro h i
    rw [Ext.mapExactFunctor_comp, h, Ext.comp_zero]
  · intro h
    have he := (finiteCoordinatesEquiv B A hB n).symm_apply_apply e
    change (∑ i, (Ext.mk₀ (sourceProjection B hB i)).comp
      ((Ext.mk₀ (sourceInclusion B hB i)).comp e (zero_add n)) (zero_add n)) = e at he
    rw [← he]
    change F.mapExtAddHom B A n _ = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    change ((Ext.mk₀ (sourceProjection B hB i)).comp
      ((Ext.mk₀ (sourceInclusion B hB i)).comp e (zero_add n)) (zero_add n)).mapExactFunctor F = 0
    rw [Ext.mapExactFunctor_comp, h, Ext.comp_zero]

/-- The actual scalar-restriction map kills a native class exactly when
its genuine alternating form pulls back to zero under the reduced
integer lattice map. This includes all degrees and all characteristics. -/
theorem finite_restriction_eq_zero_iff_alternating (a : Translation D →+ Translation D)
    (B A : ModuleCat (Laurent K D)) [FiniteDimensional K (Layers.coefficients B)]
    (hB : AugmentationAction B) (hA : AugmentationAction A) (n : ℕ) (e : Ext B A n) :
    e.mapExactFunctor (ModuleCat.restrictScalars (latticeMap K a)) = 0 ↔
      (nativeAlternatingEquiv B A hB hA n e).compLinearMap (reducedMap K a) = 0 := by
  rw [finite_restriction_eq_zero_iff_coordinates a B A hB n e,
    alternating_eq_zero_iff_cell_values]
  simp_rw [coefficient_restriction_eq_zero_iff_minors K a A hA n]
  constructor
  · intro h J
    apply (Module.finBasis K (Layers.coefficients B)).ext
    intro i
    simpa only [AlternatingMap.compLinearMap_apply, Function.comp_apply,
      reducedMap_single, nativeAlternatingEquiv_apply_basis, LinearMap.zero_apply] using h i J
  · intro h i J
    have hh := congrArg (fun g : Layers.coefficients B →ₗ[K] Layers.coefficients A =>
      g (Module.finBasis K (Layers.coefficients B) i)) (h J)
    simpa only [AlternatingMap.compLinearMap_apply, Function.comp_apply,
      reducedMap_single, nativeAlternatingEquiv_apply_basis, LinearMap.zero_apply] using hh

/-- The same native criterion expressed without any basis of the image:
the form vanishes on every tuple in the actual linear image. -/
theorem finite_restriction_eq_zero_iff_image (a : Translation D →+ Translation D)
    (B A : ModuleCat (Laurent K D)) [FiniteDimensional K (Layers.coefficients B)]
    (hB : AugmentationAction B) (hA : AugmentationAction A) (n : ℕ) (e : Ext B A n) :
    e.mapExactFunctor (ModuleCat.restrictScalars (latticeMap K a)) = 0 ↔
      ∀ v : Fin n → (Fin D → K), (∀ i, v i ∈ LinearMap.range (reducedMap K a)) →
        nativeAlternatingEquiv B A hB hA n e v = 0 := by
  rw [finite_restriction_eq_zero_iff_alternating, alternating_comp_eq_zero_iff_range]

end
end Decoupling.HighDim.KoszulLattice
