import Decoupling.HighDim.ExtValues

/-!
# Finite-source native Ext tables

Source: Lemma `lem:values`, Appendix B.2. Finite coordinate splitting is
applied to genuine derived Ext and to the proved coefficient Koszul
resolution. This file does not assume an Ext presentation or a comparison.
-/

namespace Decoupling.HighDim.ExtValues

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Preadditive CategoryTheory.Limits
open Koszul TrivialLayers
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ}

/-- Evaluation on ordered unit cells identifies actual free-module maps
with arbitrary values, over any target Laurent module. -/
def cochainValuesEquiv (A : ModuleCat (Laurent K D)) (n : ℕ) :
    ((laurentComplex K D).X n ⟶ A) ≃+ (Cell D n → A) where
  toFun f I := f (Finsupp.single I 1)
  invFun v := ModuleCat.ofHom (Finsupp.linearCombination (Laurent K D) v)
  left_inv f := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro I r
    simp only [ModuleCat.hom_ofHom, Finsupp.linearCombination_single]
    rw [← f.hom.map_smul, Finsupp.smul_single, smul_eq_mul, mul_one]
    rfl
  right_inv v := by
    funext I
    exact (Finsupp.linearCombination_single (R := Laurent K D) (v := v) 1 I).trans
      (one_smul _ _)
  map_add' f g := by ext I; rfl

/-- The explicit ordered-cell table of a native coefficient-source class. -/
def coefficientTableEquiv (A : ModuleCat (Laurent K D))
    (hA : ∀ i : Fin D, ∀ a : A, difference K i • a = 0) (n : ℕ) :
    Ext (coefficientModule K D) A n ≃+ (Cell D n → A) :=
  (coefficientExtEquiv A hA n).trans (cochainValuesEquiv A n)

@[simp] theorem coefficientTableEquiv_mk (A : ModuleCat (Laurent K D))
    (hA : ∀ i : Fin D, ∀ a : A, difference K i • a = 0) (n : ℕ)
    (f : (laurentComplex K D).X n ⟶ A) (I : Cell D n) :
    coefficientTableEquiv A hA n (coefficientMk A hA n f) I =
      f (Finsupp.single I 1) := by
  change cochainValuesEquiv A n (coefficientExtEquiv A hA n
    (coefficientMk A hA n f)) I = _
  rw [coefficientExtEquiv_mk]
  rfl

/-- Splitting a finite direct sum in the first variable of native Ext,
stated using the actual coordinate maps. -/
def sourceCoordinatesEquiv {ι : Type} [Fintype ι]
    (B A C : ModuleCat (Laurent K D))
    (inc : ι → (C ⟶ B)) (pr : ι → (B ⟶ C))
    (htotal : ∑ i, pr i ≫ inc i = 𝟙 B)
    (hself : ∀ i, inc i ≫ pr i = 𝟙 C)
    (hother : ∀ i j, i ≠ j → inc i ≫ pr j = 0) (n : ℕ) :
    Ext B A n ≃+ (ι → Ext C A n) where
  toFun e i := (Ext.mk₀ (inc i)).comp e (zero_add n)
  invFun e := ∑ i, (Ext.mk₀ (pr i)).comp (e i) (zero_add n)
  left_inv e := by
    simp only [Ext.mk₀_comp_mk₀_assoc, ← Ext.sum_comp, ← Ext.mk₀_sum,
      htotal, Ext.mk₀_id_comp]
  right_inv e := by
    ext i
    simp only [Ext.comp_sum, Ext.mk₀_comp_mk₀_assoc]
    rw [Finset.sum_eq_single i, hself, Ext.mk₀_id_comp]
    · intro j _ hji
      rw [hother i j hji.symm, Ext.mk₀_zero, Ext.zero_comp]
    · simp
  map_add' e f := by ext i; simp [Ext.comp_add]

theorem coordinate_inclusion_projection (t : ℕ) (i : Fin t) :
    coordinateInclusion K D t i ≫ coordinateProjection K D t i =
      𝟙 (coefficientModule K D) := by
  ext x
  change (@Pi.single (Fin t) (fun _ => K) _ _ i (show K from x)) i = x
  simp

theorem coordinate_inclusion_projection_ne (t : ℕ) (i j : Fin t) (h : i ≠ j) :
    coordinateInclusion K D t i ≫ coordinateProjection K D t j = 0 := by
  ext x
  change (@Pi.single (Fin t) (fun _ => K) _ _ i (show K from x)) j = 0
  simp [Ne.symm h]

/-- The actual coordinate inclusions, transported to the original module. -/
def sourceInclusion (B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (i : Fin (Module.finrank K (Layers.coefficients B))) : coefficientModule K D ⟶ B :=
  coordinateInclusion K D _ i ≫ (coordinateIso B hB).inv

/-- The actual coordinate projections of the original coefficient module. -/
def sourceProjection (B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (i : Fin (Module.finrank K (Layers.coefficients B))) : B ⟶ coefficientModule K D :=
  (coordinateIso B hB).hom ≫ coordinateProjection K D _ i

def finiteCoordinatesEquiv (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B) (n : ℕ) :
    Ext B A n ≃+ (Fin (Module.finrank K (Layers.coefficients B)) →
      Ext (coefficientModule K D) A n) :=
  sourceCoordinatesEquiv B A (coefficientModule K D)
    (sourceInclusion B hB) (sourceProjection B hB)
    (by
      simp only [sourceInclusion, sourceProjection]
      have ht := sum_projection_inclusion K D (Module.finrank K (Layers.coefficients B))
      rw [show ∑ j, ((coordinateIso B hB).hom ≫ coordinateProjection K D _ j) ≫
          (coordinateInclusion K D _ j ≫ (coordinateIso B hB).inv) =
          (coordinateIso B hB).hom ≫ (∑ j, coordinateProjection K D _ j ≫
          coordinateInclusion K D _ j) ≫ (coordinateIso B hB).inv by
            simp only [comp_sum, sum_comp, Category.assoc], ht]
      simp)
    (by intro i; simp [sourceInclusion, sourceProjection, coordinate_inclusion_projection])
    (by intro i j h; simp [sourceInclusion, sourceProjection,
      coordinate_inclusion_projection_ne _ i j h]) n

/-- Evaluation in source coordinates and ordered cell coordinates. -/
def finiteRawTableEquiv (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (hA : ∀ i : Fin D, ∀ a : A, difference K i • a = 0) (n : ℕ) :
    Ext B A n ≃+ (Fin (Module.finrank K (Layers.coefficients B)) → Cell D n → A) :=
  (finiteCoordinatesEquiv B A hB n).trans
    (AddEquiv.piCongrRight (fun _ => coefficientTableEquiv A hA n))

/-- Repack source coordinates as genuine coefficient-linear maps; the
ordered cell index stays unchanged. -/
def rawTableHomEquiv (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (n : ℕ) :
    (Fin (Module.finrank K (Layers.coefficients B)) → Cell D n → A) ≃+
      (Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A)) where
  toFun v I := (Module.finBasis K (Layers.coefficients B)).constr K (fun i => v i I)
  invFun f i I := f I (Module.finBasis K (Layers.coefficients B) i)
  left_inv v := by ext i I; simp
  right_inv f := by
    funext I
    apply (Module.finBasis K (Layers.coefficients B)).ext
    intro i
    simp
  map_add' v w := by
    ext I b
    change ((Module.finBasis K (Layers.coefficients B)).constr K
      ((fun i => (show Layers.coefficients A from v i I)) +
        (fun i => (show Layers.coefficients A from w i I)))) b = _
    rw [map_add]
    rfl

/-- Lemma 3: native Ext between finite augmentation-trivial source and
augmentation-trivial target is the complete Hom-valued ordered-cell table.
The target need not be finite dimensional. -/
def finiteExtEquiv (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (hA : AugmentationAction A) (n : ℕ) :
    Ext B A n ≃+ (Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A)) :=
  (finiteRawTableEquiv B A hB
    (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n).trans
      (rawTableHomEquiv B A n)

theorem finiteExtEquiv_eq_zero_iff (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (hA : AugmentationAction A) (n : ℕ) (e : Ext B A n) :
    finiteExtEquiv B A hB hA n e = 0 ↔ e = 0 :=
  (finiteExtEquiv B A hB hA n).map_eq_zero_iff

/-- A cochain with trivial target action sums the augmented coefficients
of a chain against its cell values. -/
theorem cochain_apply_eq_sum (A : ModuleCat (Laurent K D)) (hA : AugmentationAction A)
    (n : ℕ) (f : (laurentComplex K D).X n ⟶ A) (v : Term (Laurent K D) D n) :
    (show Layers.coefficients A from f v) =
      ∑ I : Cell D n, augmentation (v I) •
        (show Layers.coefficients A from f (Finsupp.single I 1)) := by
  classical
  have hv : v = ∑ I : Cell D n, (v I) • Finsupp.single I 1 := by
    ext J
    simp [Finsupp.smul_single]
  conv_lhs => rw [hv]
  change f.hom (∑ I : Cell D n, (v I) • Finsupp.single I 1) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro I _
  rw [f.hom.map_smul, hA]
  rfl

end
end Decoupling.HighDim.ExtValues
