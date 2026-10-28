import Decoupling.HighDim.ExtValuesTensorTable

/-!
# Evaluation of native Ext tables at arbitrary source vectors

The coefficient insertion is an actual morphism of the proved tensor
resolution. The resulting identity does not depend on a choice of basis.
-/
namespace Decoupling.HighDim.ExtValues
open CategoryTheory CategoryTheory.Abelian Koszul TrivialLayers ExtValuesTensor
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {D : ℕ}

def coefficientElement (B : ModuleCat (Laurent K D)) (hB : AugmentationAction B)
    (b : Layers.coefficients B) : coefficientModule K D ⟶ B :=
  (ModuleCat.restrictScalars augmentation).map
    (ModuleCat.ofHom (LinearMap.toSpanSingleton K (Layers.coefficients B) b)) ≫
      (coefficientEquiv B hB).toModuleIso.inv

@[simp] theorem coefficientElement_apply (B : ModuleCat (Laurent K D))
    (hB : AugmentationAction B) (b : Layers.coefficients B) (r : K) :
    coefficientElement B hB b (show coefficientModule K D from r) =
      (show B from r • b) := rfl

def tensorElementResolution (B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (b : Layers.coefficients B) :
    (projectiveResolution K D).Hom (tensorResolution B hB) (coefficientElement B hB b) where
  hom := tensorInsertionChain B b
  hom_f_zero_comp_π_f_zero := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change (tensorResolution B hB).π.f 0 (v ⊗ₜ[K] b) =
      coefficientElement B hB b (augmentationMap K D v)
    rw [tensorResolution_augmentation_tmul]
    rfl

theorem finiteExtEquiv_vector (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (hA : AugmentationAction A) (n : ℕ) (e : Ext B A n)
    (I : Cell D n) (b : Layers.coefficients B) :
    (show Layers.coefficients A from coefficientTableEquiv A
      (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n
        ((Ext.mk₀ (coefficientElement B hB b)).comp e (zero_add n)) I) =
      finiteExtEquiv B A hB hA n e I b := by
  obtain ⟨f, rfl⟩ := tensorMk_surjective B A hB
    (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n e
  rw [finiteExtEquiv_tensorMk]
  change coefficientTableEquiv A _ n ((Ext.mk₀ (coefficientElement B hB b)).comp
    ((tensorResolution B hB).extMk f (n+1) rfl
      (tensor_boundary_postcomp_zero B A
        (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n f)) (zero_add n)) I = _
  rw [ProjectiveResolution.mk₀_comp_extMk f (n+1) rfl
    (tensor_boundary_postcomp_zero B A
      (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n f)
        (tensorElementResolution B hB b)]
  change coefficientTableEquiv A
    (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n
    (coefficientMk A (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n
    (tensorInsertion B n b ≫ f)) I = _
  rw [coefficientTableEquiv_mk]
  rfl

end
end Decoupling.HighDim.ExtValues
