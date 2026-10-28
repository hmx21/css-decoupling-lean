import Decoupling.HighDim.KoszulResolution
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.DerivedCategory.Basic

/-!
# The actual higher-form toric cochain model

Source: `drafts/main.tex`, higher-form toric codes, equation `eq:toric-window`.
The term `K_k` lies in degree `j-k`, and the differential is the actual
signed Koszul boundary. The augmentation is a genuine quasi-isomorphism
to the coefficient module in degree `j`. We use the native shift
compatibility to express this derived object as `F[-j]`.
-/

namespace Decoupling.HighDim.Toric

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [CommRing K] (D : ℕ) (j : ℤ)

/-- This is the paper's actual placement of the oriented chain groups. -/
def model : CochainComplex (ModuleCat (Laurent K D)) ℤ :=
  (Koszul.laurentComplex K D).extend (ComplexShape.embeddingUpIntLE j)

def termIso (k : ℕ) : (model K D j).X (j - k) ≅
    ModuleCat.of (Laurent K D) (Koszul.Term (Laurent K D) D k) :=
  (Koszul.laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE j) rfl

/-- Every differential in the retained window is the oriented boundary,
with no characteristic-two cancellation of its signs. -/
theorem differential (k : ℕ) :
    (model K D j).d (j - (k + 1 : ℕ)) (j - k) =
      (termIso K D j (k + 1)).hom ≫
        Koszul.boundary (Laurent K D) (difference K) k ≫ (termIso K D j k).inv := by
  simpa only [model, termIso, Koszul.laurentComplex, Koszul.complex_d] using
    (Koszul.laurentComplex K D).extend_d_eq (ComplexShape.embeddingUpIntLE j)
      (i := k + 1) (j := k) (i' := j - (k + 1 : ℕ)) (j' := j - k) rfl rfl

instance model_finite (n : ℤ) : Module.Finite (Laurent K D) ((model K D j).X n) := by
  let : Module.Finite (Laurent K D) (Laurent K D) := Module.Finite.self _
  by_cases hn : ∃ k : ℕ, j - k = n
  · obtain ⟨k, rfl⟩ := hn
    exact Module.Finite.equiv (termIso K D j k).symm.toLinearEquiv
  · let : Subsingleton ((model K D j).X n) := ModuleCat.subsingleton_of_isZero
      ((Koszul.laurentComplex K D).isZero_extend_X (ComplexShape.embeddingUpIntLE j) n
        (fun k hk => hn ⟨k, hk⟩))
    exact Module.Finite.of_surjective (0 : Laurent K D →ₗ[Laurent K D] (model K D j).X n)
      (fun x => ⟨0, Subsingleton.elim _ _⟩)

instance model_free (n : ℤ) : Module.Free (Laurent K D) ((model K D j).X n) := by
  by_cases hn : ∃ k : ℕ, j - k = n
  · obtain ⟨k, rfl⟩ := hn
    exact Module.Free.of_equiv (termIso K D j k).symm.toLinearEquiv
  · let : Subsingleton ((model K D j).X n) := ModuleCat.subsingleton_of_isZero
      ((Koszul.laurentComplex K D).isZero_extend_X (ComplexShape.embeddingUpIntLE j) n
        (fun k hk => hn ⟨k, hk⟩))
    exact Module.Free.of_subsingleton _ _

instance model_projective (n : ℤ) : Projective ((model K D j).X n) := inferInstance

instance model_boundedAbove : (model K D j).IsStrictlyLE j := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  exact (Koszul.laurentComplex K D).isZero_extend_X (ComplexShape.embeddingUpIntLE j) n
    (by intro k; change j - k ≠ n; omega)

instance model_boundedBelow : (model K D j).IsStrictlyGE (j - D) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  by_cases h : ∃ k : ℕ, j - k = n
  · obtain ⟨k, rfl⟩ := h
    have : Subsingleton (Koszul.Term (Laurent K D) D k) :=
      Koszul.term_subsingleton (Laurent K D) (by omega)
    exact (ModuleCat.isZero_of_subsingleton _).of_iso (termIso K D j k)
  · exact (Koszul.laurentComplex K D).isZero_extend_X (ComplexShape.embeddingUpIntLE j) n
      (fun k hk => h ⟨k, hk⟩)

/-- The actual augmentation, extended to the indicated integer degree. -/
def augmentation : model K D j ⟶
    (CochainComplex.singleFunctor (ModuleCat (Laurent K D)) j).obj
      (Koszul.coefficientModule K D) :=
  extendMap (Koszul.resolutionAugmentation K D) (ComplexShape.embeddingUpIntLE j) ≫
    (extendSingleIso (ComplexShape.embeddingUpIntLE j) (Koszul.coefficientModule K D)
      0 j (by simp)).hom

variable [IsDomain K]

instance augmentation_quasiIso : QuasiIso (augmentation K D j) := by
  dsimp [augmentation]
  infer_instance

instance model_isGE : (model K D j).IsGE j := by
  rw [CochainComplex.isGE_iff]
  intro n hn
  rw [exactAt_iff_of_quasiIsoAt (augmentation K D j) n]
  exact ((CochainComplex.singleFunctor (ModuleCat (Laurent K D)) j).obj
    (Koszul.coefficientModule K D)).exactAt_of_isGE j n hn

/-- The single-layer derived object is proved by the actual augmentation. -/
def derivedIso : DerivedCategory.Q.obj (model K D j) ≅
    (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj
      (Koszul.coefficientModule K D) :=
  asIso (DerivedCategory.Q.map (augmentation K D j))

/-- Native shifts include the standard `(-1)^n` convention. The target
has zero differential, and the native compatibility gives exactly `F[-j]`. -/
def derivedShiftIso : DerivedCategory.Q.obj (model K D j) ≅
    ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) 0).obj
      (Koszul.coefficientModule K D))⟦-j⟧ :=
  derivedIso K D j ≪≫ ((DerivedCategory.singleFunctors (ModuleCat (Laurent K D))).shiftIso
    (-j) j 0 (by omega)).symm.app (Koszul.coefficientModule K D)

end
end Decoupling.HighDim.Toric
