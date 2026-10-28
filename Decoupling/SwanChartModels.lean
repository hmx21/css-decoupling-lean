import Decoupling.SwanExtension
import Decoupling.SwanScalarExtension
import Decoupling.IdempotentBaseChange
import Mathlib.RingTheory.Localization.LocalizationLocalization

/-!
# Actual positive and negative monic chart models

The generic charts in the opposite-chart extension are identified with the
actual monic fraction ring.  The negative chart retains the Laurent involution
in its coefficient homomorphism.
-/

namespace Decoupling.SwanChartModels

open Polynomial LaurentPolynomial MonicLocalization SwanExtension
open scoped TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (A : Type*) [CommRing A]

abbrev positiveMonic : Submonoid (Laurent A) :=
  (monicSubmonoid A).map (algebraMap A[X] (Laurent A))

abbrev PositiveGeneric := Localization (positiveMonic A)

def positiveMap : Laurent A →+* MonicFrac A :=
  (SwanScalarExtension.laurentToMonic A).comp (laurentEquiv A).toRingHom

def inverseEquiv : Laurent A ≃+* Laurent A :=
  (laurentEquiv A).toRingEquiv.trans
    (invert.toRingEquiv.trans (laurentEquiv A).symm.toRingEquiv)

def negativeMap : Laurent A →+* MonicFrac A :=
  (SwanScalarExtension.laurentToMonic A).comp
    (invert.toRingHom.comp (laurentEquiv A).toRingHom)

theorem monic_comp_toLaurent :
    (SwanScalarExtension.laurentToMonic A).comp toLaurent =
      algebraMap A[X] (MonicFrac A) := by
  apply Polynomial.ringHom_ext
  · intro a
    simp [SwanScalarExtension.constant]
  · simp

@[simp]
theorem positiveMap_algebraMap (f : A[X]) :
    positiveMap A (algebraMap A[X] (Laurent A) f) = algebraMap A[X] (MonicFrac A) f := by
  change SwanScalarExtension.laurentToMonic A (laurentEquiv A _) = _
  rw [laurentEquiv_algebraMap]
  exact DFunLike.congr_fun (monic_comp_toLaurent A) f

@[simp]
theorem inverseEquiv_algebraMap (f : A[X]) :
    inverseEquiv A (algebraMap A[X] (Laurent A) f) = negativePolynomial A f := by
  change (laurentEquiv A).symm (invert (laurentEquiv A _)) = _
  rw [laurentEquiv_algebraMap]
  rfl

@[simp]
theorem inverseEquiv_symm : (inverseEquiv A).symm = inverseEquiv A := by
  ext x
  rfl

theorem negativeMap_eq : negativeMap A = (positiveMap A).comp (inverseEquiv A).toRingHom := by
  ext x
  exact congrArg (SwanScalarExtension.laurentToMonic A) ((laurentEquiv A).apply_symm_apply _).symm

/-- The positive chart uses the ordinary coefficient map. -/
abbrev positiveAlgebra : Algebra (Laurent A) (MonicFrac A) := (positiveMap A).toAlgebra

/-- The negative chart uses inversion of the Laurent variable. -/
abbrev negativeAlgebra : Algebra (Laurent A) (MonicFrac A) := (negativeMap A).toAlgebra

local instance : Algebra (Laurent A) (MonicFrac A) := positiveAlgebra A

local instance positiveTower : IsScalarTower A[X] (Laurent A) (MonicFrac A) :=
  IsScalarTower.of_algebraMap_eq' (by
    apply RingHom.ext
    intro f
    exact (positiveMap_algebraMap A f).symm)

/-- The actual positive chart is the localization at the image of the monics. -/
theorem positive_isLocalization : IsLocalization (positiveMonic A) (MonicFrac A) := by
  apply IsLocalization.isLocalization_of_submonoid_le (Laurent A) (MonicFrac A)
    (Submonoid.powers (X : A[X])) (monicSubmonoid A)
  rintro _ ⟨n, rfl⟩
  exact Polynomial.monic_X.pow n

/-- Canonical and concrete positive generic rings agree over the Laurent ring. -/
def positiveEquiv : PositiveGeneric A ≃ₐ[Laurent A] MonicFrac A := by
  letI := positive_isLocalization A
  exact IsLocalization.algEquiv (positiveMonic A) _ _

/-- The negative chart is the same fraction ring with the explicit inverse-variable action. -/
theorem negative_isLocalization :
    letI := negativeAlgebra A
    IsLocalization (negativeMonic A) (MonicFrac A) := by
  let := positive_isLocalization A
  have h := IsLocalization.isLocalization_of_base_ringEquiv
    (positiveMonic A) (MonicFrac A) (inverseEquiv A)
  have hm : (positiveMonic A).map (inverseEquiv A) = negativeMonic A := by
    ext x
    constructor
    · rintro ⟨y, ⟨f, hf, rfl⟩, rfl⟩
      exact ⟨f, hf, (inverseEquiv_algebraMap A f).symm⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨algebraMap A[X] (Laurent A) f, ⟨f, hf, rfl⟩,
        inverseEquiv_algebraMap A f⟩
  rw [hm] at h
  convert h using 1
  apply Algebra.algebra_ext
  intro x
  change negativeMap A x = positiveMap A ((inverseEquiv A).symm x)
  rw [inverseEquiv_symm]
  exact DFunLike.congr_fun (negativeMap_eq A) x

/-- Actual negative generic localization, with its Laurent scalar action retained. -/
def negativeEquiv :
    letI := negativeAlgebra A
    NegativeGeneric A ≃ₐ[Laurent A] MonicFrac A := by
  letI := negativeAlgebra A
  letI := negative_isLocalization A
  exact IsLocalization.algEquiv (negativeMonic A) _ _


/-- A free actual negative-chart matrix image supplies the native input used
by the opposite-chart extension. -/
theorem negative_free_of_image_free {n : ℕ}
    (E : Matrix (Fin n) (Fin n) (Laurent A)) (hE : E * E = E)
    (hf : Module.Free (MonicFrac A)
      (LinearMap.range (E.map (negativeMap A)).mulVecLin)) :
    Module.Free (NegativeGeneric A)
      (LocalizedModule (negativeMonic A) (IdempotentBaseChange.Image E)) := by
  let : Algebra (Laurent A) (MonicFrac A) := negativeAlgebra A
  let : IsLocalization (negativeMonic A) (MonicFrac A) := negative_isLocalization A
  let : Module (MonicFrac A)
      (LocalizedModule (negativeMonic A) (IdempotentBaseChange.Image E)) :=
    LocalizedModule.moduleOfIsLocalization (S := negativeMonic A) (T := MonicFrac A)
      (M := IdempotentBaseChange.Image E)
  let : Module.Free (MonicFrac A)
      (LocalizedModule (negativeMonic A) (IdempotentBaseChange.Image E)) :=
    IdempotentBaseChange.free_localized_of_free_image (B := MonicFrac A) E hE (negativeMonic A)
      (P := LocalizedModule (negativeMonic A) (IdempotentBaseChange.Image E))
      (LocalizedModule.mkLinearMap (negativeMonic A) (IdempotentBaseChange.Image E)) hf
  exact MonicChartExtension.free_of_localizationModelEquiv (negativeMonic A)
    (MonicFrac A) (NegativeGeneric A)
    (M := LocalizedModule (negativeMonic A) (IdempotentBaseChange.Image E))
    (N := LocalizedModule (negativeMonic A) (IdempotentBaseChange.Image E))
    (LinearEquiv.refl (Laurent A)
      (LocalizedModule (negativeMonic A) (IdempotentBaseChange.Image E)))

/-- Positive native localized freeness has the same exact model identification. -/
theorem positive_free_of_image_free {n : ℕ}
    (E : Matrix (Fin n) (Fin n) (Laurent A)) (hE : E * E = E)
    (hf : Module.Free (MonicFrac A)
      (LinearMap.range (E.map (positiveMap A)).mulVecLin)) :
    Module.Free (MonicFrac A)
      (MonicFrac A ⊗[Laurent A] IdempotentBaseChange.Image E) := by
  let := hf
  exact Module.Free.of_equiv (IdempotentBaseChange.imageEquiv E hE).symm

@[simp]
theorem negativeMap_symm_apply (p : LaurentPolynomial A) :
    negativeMap A ((laurentEquiv A).symm p) =
      SwanScalarExtension.laurentToMonic A (invert p) := by
  change SwanScalarExtension.laurentToMonic A (invert (laurentEquiv A _)) = _
  rw [AlgEquiv.apply_symm_apply]

/-- The coefficient map of the native negative chart is literally the
inverted Laurent matrix followed by the monic-fraction map. -/
theorem negative_mapped_matrix {n : ℕ}
    (E : Matrix (Fin n) (Fin n) (LaurentPolynomial A)) :
    (E.map (laurentEquiv A).symm.toRingHom).map (negativeMap A) =
      (E.map invert.toRingHom).map (SwanScalarExtension.laurentToMonic A) := by
  funext i j
  exact negativeMap_symm_apply A (E i j)

/-- Lower-dimensional freeness supplies the actual negative localization
input, including both matrix scalar extension and localization-model transport. -/
theorem negative_free_of_lower (K G : Type*) [CommRing K] [Nontrivial K] [AddCommMonoid G]
    (hgeneric : ProjectiveFreeness.IdempotentCriterion (AddMonoidAlgebra (MonicFrac K) G))
    {n : ℕ} (E : Matrix (Fin n) (Fin n)
      (LaurentPolynomial (SwanScalarExtension.CoefficientLaurent K G)))
    (hE : E * E = E) :
    Module.Free (NegativeGeneric (SwanScalarExtension.CoefficientLaurent K G))
      (LocalizedModule (negativeMonic (SwanScalarExtension.CoefficientLaurent K G))
        (IdempotentBaseChange.Image
          (E.map (laurentEquiv (SwanScalarExtension.CoefficientLaurent K G)).symm.toRingHom))) := by
  apply negative_free_of_image_free _ _ (by rw [← Matrix.map_mul, hE])
  rw [negative_mapped_matrix]
  exact SwanScalarExtension.opposite_generic_image_free K G hgeneric E hE


@[simp]
theorem positiveMap_symm_apply (p : LaurentPolynomial A) :
    positiveMap A ((laurentEquiv A).symm p) =
      SwanScalarExtension.laurentToMonic A p := by
  change SwanScalarExtension.laurentToMonic A (laurentEquiv A _) = _
  rw [AlgEquiv.apply_symm_apply]

theorem positive_mapped_matrix {n : ℕ}
    (E : Matrix (Fin n) (Fin n) (LaurentPolynomial A)) :
    (E.map (laurentEquiv A).symm.toRingHom).map (positiveMap A) =
      E.map (SwanScalarExtension.laurentToMonic A) := by
  funext i j
  exact positiveMap_symm_apply A (E i j)

/-- Lower-dimensional freeness also supplies the actual tensor-product
positive generic chart of the canonical Laurent idempotent image. -/
theorem positive_free_of_lower (K G : Type*) [CommRing K] [Nontrivial K] [AddCommMonoid G]
    (hgeneric : ProjectiveFreeness.IdempotentCriterion (AddMonoidAlgebra (MonicFrac K) G))
    {n : ℕ} (E : Matrix (Fin n) (Fin n)
      (LaurentPolynomial (SwanScalarExtension.CoefficientLaurent K G)))
    (hE : E * E = E) :
    Module.Free (MonicFrac (SwanScalarExtension.CoefficientLaurent K G))
      (MonicFrac (SwanScalarExtension.CoefficientLaurent K G) ⊗[
        Laurent (SwanScalarExtension.CoefficientLaurent K G)]
        IdempotentBaseChange.Image
          (E.map (laurentEquiv (SwanScalarExtension.CoefficientLaurent K G)).symm.toRingHom)) := by
  apply positive_free_of_image_free _ _ (by rw [← Matrix.map_mul, hE])
  rw [positive_mapped_matrix]
  exact SwanScalarExtension.generic_image_free K G hgeneric E hE

end
end Decoupling.SwanChartModels
