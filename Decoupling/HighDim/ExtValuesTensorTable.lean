import Decoupling.HighDim.ExtValuesTensor
import Decoupling.HighDim.ExtValuesAlternating

/-!
# Cell evaluation of the actual tensor representative

This identifies the finite native Ext table with evaluation of the unique
cochain on `K_n ⊗_K B`; it also proves independence from the auxiliary
coefficient basis used to construct that resolution.
-/

namespace Decoupling.HighDim.ExtValuesTensor

open CategoryTheory CategoryTheory.Abelian Koszul TrivialLayers ExtValues
open scoped TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ}

/-- Inserting a coefficient commutes with every actual tensor differential. -/
def tensorInsertionChain (B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (b : Layers.coefficients B) :
    laurentComplex K D ⟶ tensorComplex B where
  f n := tensorInsertion B n b
  comm' i j h := by
    change j + 1 = i at h
    subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change (tensorComplex B).d (j + 1) j (v ⊗ₜ[K] b) =
      (show Term (Laurent K D) D j from (laurentComplex K D).d (j + 1) j v) ⊗ₜ[K] b
    rw [tensorComplex_d_tmul]
    rw [show (laurentComplex K D).d (j + 1) j =
      boundary (Laurent K D) (difference K) j from complex_d _ _ _]
    rfl

/-- Coefficient insertion is precisely the original source coordinate map. -/
theorem sourceInclusion_apply (B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (i : Fin (Module.finrank K (Layers.coefficients B))) (r : K) :
    sourceInclusion B hB i (show coefficientModule K D from r) =
      (show B from r • Module.finBasis K (Layers.coefficients B) i) := by
  apply (coordinateIso B hB).toLinearEquiv.injective
  change (coordinateIso B hB).hom ((coordinateIso B hB).inv (Pi.single i r)) = _
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
  change Pi.single i r = (Module.finBasis K (Layers.coefficients B)).repr
    (r • Module.finBasis K (Layers.coefficients B) i)
  simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_single,
    smul_eq_mul, mul_one]
  exact (Finsupp.single_eq_pi_single i r).symm

/-- The insertion on a coefficient basis vector is an actual morphism of
projective resolutions, covering the original module inclusion. -/
def tensorInsertionResolution (B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (i : Fin (Module.finrank K (Layers.coefficients B))) :
    (projectiveResolution K D).Hom (tensorResolution B hB) (sourceInclusion B hB i) where
  hom := tensorInsertionChain B (Module.finBasis K (Layers.coefficients B) i)
  hom_f_zero_comp_π_f_zero := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change (tensorResolution B hB).π.f 0
      (v ⊗ₜ[K] Module.finBasis K (Layers.coefficients B) i) =
      sourceInclusion B hB i (augmentationMap K D v)
    rw [tensorResolution_augmentation_tmul]
    exact (sourceInclusion_apply B hB i _).symm

/-- The same actual cochain is coefficient-linear, using the original
constant Laurent action on its target. -/
def tensorCochainCoefficientMap (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (n : ℕ)
    (f : (tensorComplex B).X n ⟶ A) : TensorTerm B n →ₗ[K] Layers.coefficients A where
  toFun z := f z
  map_add' x y := f.hom.map_add x y
  map_smul' r z := by
    change f.hom (r • z) = constant (D := D) r • f.hom z
    rw [← f.hom.map_smul]
    congr 1
    exact (IsScalarTower.algebraMap_smul (Laurent K D) r z).symm

/-- The Hom-valued table obtained by literal evaluation on ordered unit
cells of the actual tensor representative. -/
def tensorValues (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (n : ℕ)
    (f : (tensorComplex B).X n ⟶ A) (I : Cell D n) :
    Layers.coefficients B →ₗ[K] Layers.coefficients A :=
  (tensorCochainCoefficientMap B A n f).comp
    (TensorProduct.mk K (Term (Laurent K D) D n) (Layers.coefficients B) (Finsupp.single I 1))

@[simp] theorem tensorValues_apply (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (n : ℕ)
    (f : (tensorComplex B).X n ⟶ A) (I : Cell D n) (b : Layers.coefficients B) :
    tensorValues B A n f I b = f (Finsupp.single I 1 ⊗ₜ[K] b) := rfl

/-- The finite native Ext equivalence is exactly the manuscript's table
of values of its unique actual tensor Koszul representative. -/
theorem finiteExtEquiv_tensorMk (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (hA : AugmentationAction A) (n : ℕ) (f : (tensorComplex B).X n ⟶ A) :
    finiteExtEquiv B A hB hA n
      (tensorMk B A hB (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n f) =
        tensorValues B A n f := by
  funext I
  apply (Module.finBasis K (Layers.coefficients B)).ext
  intro i
  rw [finiteExtEquiv_apply_basis]
  change coefficientTableEquiv A _ n ((Ext.mk₀ (sourceInclusion B hB i)).comp
    ((tensorResolution B hB).extMk f (n + 1) rfl
      (tensor_boundary_postcomp_zero B A
        (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n f))
          (zero_add n)) I = _
  rw [ProjectiveResolution.mk₀_comp_extMk f (n + 1) rfl
    (tensor_boundary_postcomp_zero B A
      (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n f)
        (tensorInsertionResolution B hB i)]
  change coefficientTableEquiv A
    (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n
      (coefficientMk A
        (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n
    (tensorInsertion B n (Module.finBasis K (Layers.coefficients B) i) ≫ f)) I = _
  rw [coefficientTableEquiv_mk]
  rfl

/-- Evaluation of the actual unique tensor representative of any native
Ext class gives the same ordered-cell table, for every source vector. -/
theorem tensorRepresentative_value (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (hA : AugmentationAction A) (n : ℕ) (e : Ext B A n)
    (I : Cell D n) (b : Layers.coefficients B) :
    finiteExtEquiv B A hB hA n e I b =
      tensorExtEquiv B A hB
        (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n e
          (Finsupp.single I 1 ⊗ₜ[K] b) := by
  obtain ⟨f, rfl⟩ := tensorMk_surjective B A hB
    (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n e
  rw [finiteExtEquiv_tensorMk, tensorExtEquiv_mk]
  rfl

end
end Decoupling.HighDim.ExtValuesTensor
