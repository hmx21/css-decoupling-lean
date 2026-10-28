import Decoupling.HighDim.KoszulContractionFormula
import Decoupling.HighDim.ExtValuesFunctor

/-!
# The contraction recovers the original Ext representative

The augmentation identity is proved on the actual tensor resolution,
with ordered-cell normalization +1 and no choice of a new Ext class.
-/

namespace Decoupling.HighDim.KoszulContraction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open Koszul TrivialLayers ExtValuesTensor CochainComplex.HomComplex Toric.Hodge
open scoped TensorProduct
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type} [Field K] {D : ℕ}

def castCell {n m : ℕ} (h : n = m) (I : Cell D n) : Cell D m := h ▸ I

@[simp] theorem directions_castCell {n m : ℕ} (h : n = m) (I : Cell D n) :
    directions (castCell h I) = directions I := by subst m; rfl

variable (B A : ModuleCat (Laurent K D))
  [FiniteDimensional K (Layers.coefficients B)]
  [FiniteDimensional K (Layers.coefficients A)]
  (hB : AugmentationAction B) (hA : AugmentationAction A)

theorem tensorDegreeCast_tmul {n m : ℕ} (h : n = m) (I : Cell D n)
    (b : Layers.coefficients B) :
    ((tensorComplex B).XIsoOfEq h).hom (Finsupp.single I 1 ⊗ₜ[K] b) =
      Finsupp.single (castCell h I) 1 ⊗ₜ[K] b := by
  subst m
  rfl

def topComponent (n : ℕ)
    (f : Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A)) :
    (tensorComplex B).X n ⟶ (tensorComplex A).X 0 :=
  ((tensorComplex B).XIsoOfEq (Nat.zero_add n).symm).hom ≫ tableComponent B A hB n f 0

theorem topComponent_single (n : ℕ)
    (f : Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A))
    (I : Cell D n) (b : Layers.coefficients B) :
    topComponent B A hB n f (Finsupp.single I 1 ⊗ₜ[K] b) =
      Finsupp.single (zeroCell D) 1 ⊗ₜ[K] f I b := by
  change tableComponent B A hB n f 0
    (((tensorComplex B).XIsoOfEq _).hom (Finsupp.single I 1 ⊗ₜ[K] b)) = _
  rw [tensorDegreeCast_tmul, tableComponent_single]
  rw [Finset.sum_eq_single I]
  · rw [deletion_equal_directions n I _ (directions_castCell _ I).symm]
    simp only [deletionValue, pow_zero]
  · intro I' _ hne
    have hn : deletion n I' 0 (castCell (Nat.zero_add n).symm I) = none := by
      by_contra hh
      have hs := (deletion_ne_none_iff n I' 0 _).mp hh
      rw [directions_castCell] at hs
      have he : directions I' = directions I :=
        Finset.eq_of_subset_of_card_le hs (by simp only [directions_card]; omega)
      exact hne (directions_injective he)
    rw [hn]
    rfl
  · simp

theorem topComponent_augmentation_single (n : ℕ)
    (f : Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A))
    (I : Cell D n) (b : Layers.coefficients B) :
    (topComponent B A hB n f ≫ (resolution A hA).π.f 0)
      (Finsupp.single I 1 ⊗ₜ[K] b) = f I b := by
  change (resolution A hA).π.f 0 (topComponent B A hB n f (Finsupp.single I 1 ⊗ₜ[K] b)) = _
  rw [topComponent_single, tensorResolution_augmentation_tmul, zeroTermEquiv_single]
  simp only [map_one, one_smul]

omit [FiniteDimensional K (Layers.coefficients A)] in
/-- Laurent-linear maps from the literal tensor term are determined by
their ordered unit-cell values on arbitrary coefficient vectors. -/
theorem tensorTerm_hom_ext (n : ℕ) (f g : (tensorComplex B).X n ⟶ A)
    (h : ∀ I : Cell D n, ∀ b : Layers.coefficients B,
      f (Finsupp.single I 1 ⊗ₜ[K] b) = g (Finsupp.single I 1 ⊗ₜ[K] b)) : f = g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp_all only [map_add]
  | tmul v b =>
    have he : tensorInsertion B n b ≫ f = tensorInsertion B n b ≫ g := by
      apply ModuleCat.hom_ext
      apply (Finsupp.basisSingleOne : Module.Basis (Cell D n) (Laurent K D)
        (Term (Laurent K D) D n)).ext
      intro I
      exact h I b
    exact congrArg (fun k : (laurentComplex K D).X n ⟶ A => k v) he

/-- Augmentation of the explicit contraction is precisely the original
cochain, not just a cohomologous representative. -/
theorem topComponent_augmentation (n : ℕ) (f : (tensorComplex B).X n ⟶ A) :
    topComponent B A hB n (tensorValues B A n f) ≫ (resolution A hA).π.f 0 = f := by
  apply tensorTerm_hom_ext B A n
  intro I b
  exact topComponent_augmentation_single B A hB hA n (tensorValues B A n f) I b

end
end Decoupling.HighDim.KoszulContraction
