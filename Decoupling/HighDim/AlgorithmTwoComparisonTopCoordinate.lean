import Decoupling.HighDim.AlgorithmTwoComparisonStackAugmentation

/-!
# Literal augmentation of the empty Koszul cell

This identifies the top generator used in the prescribed equations
with the unit coordinate of the genuine single coefficient module.
-/
namespace Decoupling.HighDim.AlgorithmTwoComparison
open CategoryTheory CategoryTheory.Limits HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
variable (K : Type) [Field K] (D : ℕ)

theorem toricAugmentation_top_coordinate (j : ℤ) :
    (singleObjXSelf (ComplexShape.up ℤ) j (Koszul.coefficientModule K D)).hom
      ((Toric.augmentation K D j).f j (toricTop K D j)) = (1 : K) := by
  have h := (by simp : (ComplexShape.embeddingUpIntLE j).f 0 = j)
  have he : (Toric.augmentation K D j).f j ≫
      (singleObjXSelf (ComplexShape.up ℤ) j (Koszul.coefficientModule K D)).hom =
    ((Koszul.laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE j) h).hom ≫
      Koszul.augmentationMap K D := by
    rw [Toric.augmentation, HomologicalComplex.comp_f, extendMap_f _ _ h,
      extendSingleIso_hom_f]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc,
      Koszul.resolutionAugmentation_zero]
    rfl
  change (((Toric.augmentation K D j).f j) ≫
    (singleObjXSelf (ComplexShape.up ℤ) j (Koszul.coefficientModule K D)).hom) (toricTop K D j) = _
  rw [he]
  have hequiv (v : (Toric.model K D j).X j) :
      toricTopEquiv K D j v = Koszul.zeroTermEquiv (Laurent K D)
        (((Koszul.laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE j) h).hom v) := by
    rfl
  change augmentation (Koszul.zeroTermEquiv (Laurent K D)
    (((Koszul.laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE j) h).hom
      (toricTop K D j))) = (1 : K)
  rw [← hequiv]
  rw [toricTop, LinearEquiv.apply_symm_apply, map_one]

theorem toricAugmentation_top (j : ℤ) :
    (Toric.augmentation K D j).f j (toricTop K D j) =
      (singleObjXSelf (ComplexShape.up ℤ) j (Koszul.coefficientModule K D)).inv (1 : K) := by
  apply (ModuleCat.mono_iff_injective
    (singleObjXSelf (ComplexShape.up ℤ) j (Koszul.coefficientModule K D)).hom).mp inferInstance
  rw [toricAugmentation_top_coordinate]
  change (1 : K) =
    ((singleObjXSelf (ComplexShape.up ℤ) j (Koszul.coefficientModule K D)).inv ≫
      (singleObjXSelf (ComplexShape.up ℤ) j (Koszul.coefficientModule K D)).hom) (1 : K)
  rw [Iso.inv_hom_id]
  rfl

local instance : HasFiniteBiproducts (CochainComplex (ModuleCat (Laurent K D)) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The image is the literal unit coordinate in the indicated copy
of the zero-differential stack, even when degrees are repeated. -/
theorem stackTopImage_eq_inclusion {ι : Type} [Fintype ι] (forms : ι → ℕ) (i : ι) :
    stackTopImage K D forms i =
      (biproduct.ι (stackSingleFamily K D forms) i).f (forms i + 1)
        ((singleObjXSelf (ComplexShape.up ℤ) (forms i + 1) (Koszul.coefficientModule K D)).inv
          (1 : K)) := by
  change ((biproduct.ι (fun i => Toric.model K D (forms i + 1)) i).f (forms i + 1) ≫
    (stackAugmentation K D forms).f (forms i + 1)) (toricTop K D (forms i + 1)) = _
  rw [← HomologicalComplex.comp_f]
  dsimp only [stackAugmentation]
  rw [biproduct.ι_map, HomologicalComplex.comp_f]
  change (biproduct.ι (stackSingleFamily K D forms) i).f (forms i + 1)
    ((Toric.augmentation K D (forms i + 1)).f (forms i + 1) (toricTop K D (forms i + 1))) = _
  rw [toricAugmentation_top]

end
end Decoupling.HighDim.AlgorithmTwoComparison
