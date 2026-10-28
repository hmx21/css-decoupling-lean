import Decoupling.HighDim.KoszulLatticeValues
import Decoupling.HighDim.ExtValuesNaturality

/-!
# Complete Hom-valued native restriction table

Scalar restriction preserves the coefficient vector spaces through the
identity on elements. Under these explicit identifications every actual
native restricted Ext table entry is the integer-minors pullback, not
merely a test for its vanishing.
-/
namespace Decoupling.HighDim.KoszulLattice
open CategoryTheory CategoryTheory.Abelian Koszul ExtValues TrivialLayers
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] {D : ℕ}

def latticeCoefficientsEquiv (a : Translation D →+ Translation D) (M : ModuleCat (Laurent K D)) :
    Layers.coefficients ((ModuleCat.restrictScalars (latticeMap K a)).obj M) ≃ₗ[K]
      Layers.coefficients M where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' r x := by
    change latticeMap K a (constant r) • (show M from x) = constant (D := D) r • (show M from x)
    rw [latticeMap_constant]

instance latticeCoefficients_finite (a : Translation D →+ Translation D)
    (M : ModuleCat (Laurent K D)) [FiniteDimensional K (Layers.coefficients M)] :
    FiniteDimensional K (Layers.coefficients ((ModuleCat.restrictScalars (latticeMap K a)).obj M)) :=
  Module.Finite.equiv (latticeCoefficientsEquiv K a M).symm

theorem coefficientElement_restriction (a : Translation D →+ Translation D)
    (B : ModuleCat (Laurent K D)) (hB : AugmentationAction B) (b : Layers.coefficients B) :
    coefficientElement ((ModuleCat.restrictScalars (latticeMap K a)).obj B)
      (restrictedAugmentationAction K a B hB) ((latticeCoefficientsEquiv K a B).symm b) =
      (latticeCoefficientIso K a).hom ≫
        (ModuleCat.restrictScalars (latticeMap K a)).map (coefficientElement B hB b) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change latticeMap K a (constant (show K from r)) • (show B from b) =
    constant (D := D) (show K from r) • (show B from b)
  rw [latticeMap_constant]

/-- Full minors formula for the actual native restriction of an arbitrary
finite-source augmentation-trivial Ext class, evaluated on every source
vector. No choices of coarse coefficient bases appear in the result. -/
theorem finite_restriction_table (a : Translation D →+ Translation D)
    (B A : ModuleCat (Laurent K D)) [FiniteDimensional K (Layers.coefficients B)]
    (hB : AugmentationAction B) (hA : AugmentationAction A) (n : ℕ) (e : Ext B A n)
    (J : Cell D n) (b : Layers.coefficients B) :
    latticeCoefficientsEquiv K a A
      (finiteExtEquiv ((ModuleCat.restrictScalars (latticeMap K a)).obj B)
        ((ModuleCat.restrictScalars (latticeMap K a)).obj A)
        (restrictedAugmentationAction K a B hB) (restrictedAugmentationAction K a A hA) n
        (e.mapExactFunctor (ModuleCat.restrictScalars (latticeMap K a))) J
        ((latticeCoefficientsEquiv K a B).symm b)) =
      ∑ I : Cell D n, Matrix.det (fun k l => (a (translationBasis (J k)) (I l) : K)) •
        finiteExtEquiv B A hB hA n e I b := by
  rw [← finiteExtEquiv_vector]
  rw [coefficientElement_restriction K a B hB b, ← Ext.mk₀_comp_mk₀_assoc,
    ← Ext.mapExactFunctor_mk₀, ← Ext.mapExactFunctor_comp]
  change (show Layers.coefficients A from
    coefficientTableEquiv ((ModuleCat.restrictScalars (latticeMap K a)).obj A)
      (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction _
        (restrictedAugmentationAction K a A hA)) n
      (coefficientRestriction K a A n
        ((Ext.mk₀ (coefficientElement B hB b)).comp e (zero_add n))) J) = _
  rw [coefficientRestriction_table K a A hA]
  apply Finset.sum_congr rfl
  intro I _
  rw [finiteExtEquiv_vector]

end
end Decoupling.HighDim.KoszulLattice
