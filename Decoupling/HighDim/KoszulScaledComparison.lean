import Decoupling.HighDim.KoszulRestriction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-! # A genuine quasi-isomorphism for the scaled Laurent Koszul resolution -/

namespace Decoupling.HighDim.Koszul

open CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (A : Type*) [CommRing A] {D : ℕ}

/-- The actual semilinear diagonal comparison, with arbitrary compatible weights. -/
def restrictedComparison (φ : A →+* A) (w c : Fin D → A)
    (h : ∀ i, φ (w i) = w i * c i) :
    complex A w ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex (.down ℕ)).obj
      (complex A w) where
  f k := scalarChangeTerm A φ k ≫
    (ModuleCat.restrictScalars φ).map (comparisonTerm A c k)
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    simp only [Functor.mapHomologicalComplex_obj_d, complex_d]
    rw [Category.assoc, ← Functor.map_comp, comparisonTerm_boundary,
      Functor.map_comp, ← Category.assoc, ← funext h, scalarChangeTerm_boundary]
    simp only [Category.assoc]

@[simp] theorem restrictedComparison_f (φ : A →+* A) (w c : Fin D → A)
    (h : ∀ i, φ (w i) = w i * c i) (k : ℕ) :
    (restrictedComparison A φ w c h).f k = scalarChangeTerm A φ k ≫
      (ModuleCat.restrictScalars φ).map (comparisonTerm A c k) := rfl

@[simp] theorem restrictedComparison_single (φ : A →+* A) (w c : Fin D → A)
    (h : ∀ i, φ (w i) = w i * c i) (k : ℕ) (I : Cell D k) (a : A) :
    (restrictedComparison A φ w c h).f k (Finsupp.single I a) =
      Finsupp.single I (φ a * comparisonFactor A c I) := by
  change (comparisonTerm A c k).hom
    (scalarChangeTerm A φ k (Finsupp.single I a)) = _
  rw [scalarChangeTerm_single, comparisonTerm_single]

variable (K : Type*) [CommRing K] (D p : ℕ) [Fact p.Prime] [CharP K p]

/-- One p-scaling step, as a native chain map from the coarse resolution
into the scalar restriction of the fine resolution. -/
def scalingComparison : laurentComplex K D ⟶
    ((ModuleCat.restrictScalars (scaling K D p)).mapHomologicalComplex (.down ℕ)).obj
      (laurentComplex K D) :=
  restrictedComparison (Laurent K D) (scaling K D p) (difference K)
    (fun i => difference K i ^ (p - 1)) (by
      intro i
      rw [scaling_difference, ← pow_succ', Nat.sub_add_cancel (Fact.out : p.Prime).one_lt.le])

/-- The coefficient action is unchanged under actual p-scaling. -/
def scalingCoefficientIso : coefficientModule K D ≅
    (ModuleCat.restrictScalars (scaling K D p)).obj (coefficientModule K D) :=
  LinearEquiv.toModuleIso (show coefficientModule K D ≃ₗ[Laurent K D]
    (ModuleCat.restrictScalars (scaling K D p)).obj (coefficientModule K D) from {
    toFun x := x
    invFun x := x
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' r x := by
      change ((augmentation : Laurent K D →+* K) r) * (show K from x) =
        ((augmentation : Laurent K D →+* K) (scaling K D p r)) * (show K from x)
      rw [augmentation_scaling] })

/-- The chain comparison induces the identity map on the actual coefficient module. -/
theorem scalingComparison_augmentation_zero :
    (scalingComparison K D p).f 0 ≫
      (ModuleCat.restrictScalars (scaling K D p)).map (augmentationMap K D) =
      augmentationMap K D ≫ (scalingCoefficientIso K D p).hom := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro I a
  change augmentationMap K D ((scalingComparison K D p).f 0 (Finsupp.single I a)) =
    augmentation (zeroTermEquiv (Laurent K D) (Finsupp.single I a))
  rw [show (scalingComparison K D p).f 0 (Finsupp.single I a) =
      Finsupp.single I (scaling K D p a *
        comparisonFactor (Laurent K D) (fun i => difference K i ^ (p - 1)) I) from
      restrictedComparison_single _ _ _ _ _ _ _ _]
  simp [comparisonFactor]

/-- The augmented comparison, including the native single-complex transport. -/
theorem scalingComparison_augmentation :
    scalingComparison K D p ≫
      ((ModuleCat.restrictScalars (scaling K D p)).mapHomologicalComplex (.down ℕ)).map
        (resolutionAugmentation K D) ≫
      (HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.restrictScalars (scaling K D p)) (.down ℕ) 0).hom.app
        (coefficientModule K D) =
    resolutionAugmentation K D ≫
      (ChainComplex.single₀ (ModuleCat (Laurent K D))).map (scalingCoefficientIso K D p).hom := by
  apply HomologicalComplex.to_single_hom_ext
  simpa using scalingComparison_augmentation_zero K D p

/-- Every positive comparison component is killed by every linear map into
an augmentation-annihilated target. This is an equality of the actual
restricted morphisms, with the semilinear coefficient map included. -/
theorem scalingComparison_postcomp_zero (B : ModuleCat (Laurent K D))
    (hB : ∀ i : Fin D, ∀ b : B, difference K i • b = 0)
    (k : ℕ) (f : (laurentComplex K D).X (k + 1) ⟶ B) :
    (scalingComparison K D p).f (k + 1) ≫
      (ModuleCat.restrictScalars (scaling K D p)).map f = 0 := by
  have he : p - 1 = (p - 2) + 1 := by have := (Fact.out : p.Prime).two_le; omega
  have h : comparisonTerm (Laurent K D)
      (fun i => difference K i ^ (p - 1)) (k + 1) ≫ f = 0 := by
    apply ModuleCat.hom_ext
    rw [ModuleCat.hom_comp, he]
    exact postcomp_comparisonTerm_eq_zero (Laurent K D) (difference K) hB (p - 2) k f.hom
  change (scalarChangeTerm (Laurent K D) (scaling K D p) (k + 1) ≫
    (ModuleCat.restrictScalars (scaling K D p)).map
      (comparisonTerm (Laurent K D) (fun i => difference K i ^ (p - 1)) (k + 1))) ≫
        (ModuleCat.restrictScalars (scaling K D p)).map f = 0
  rw [Category.assoc, ← Functor.map_comp, h, Functor.map_zero, comp_zero]

variable [IsDomain K]

instance scalingComparison_quasiIso : QuasiIso (scalingComparison K D p) := by
  let f := ((ModuleCat.restrictScalars (scaling K D p)).mapHomologicalComplex (.down ℕ)).map
    (resolutionAugmentation K D) ≫
    (HomologicalComplex.singleMapHomologicalComplex
      (ModuleCat.restrictScalars (scaling K D p)) (.down ℕ) 0).hom.app (coefficientModule K D)
  have : QuasiIso (scalingComparison K D p ≫ f) := by
    dsimp [f]
    rw [scalingComparison_augmentation]
    infer_instance
  exact quasiIso_of_comp_right (scalingComparison K D p) f

end
end Decoupling.HighDim.Koszul
