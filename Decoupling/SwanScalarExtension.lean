import Decoupling.ProjectiveFreeness
import Decoupling.MonicLocalization
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Scalar maps for induction on the number of Laurent variables

The extra Laurent variable maps to the invertible polynomial variable in the
actual monic localization. Reordering the variables and passing coefficients
to the rational-function field are compared as genuine ring homomorphisms.
-/

namespace Decoupling.SwanScalarExtension

open MonicLocalization ProjectiveFreeness
open scoped LaurentPolynomial

noncomputable section

variable (A : Type*) [CommRing A]

def constant : A →+* MonicFrac A :=
  (algebraMap (Polynomial A) (MonicFrac A)).comp Polynomial.C

def variableUnit : (MonicFrac A)ˣ :=
  (IsLocalization.map_units (MonicFrac A)
    (⟨Polynomial.X, Polynomial.monic_X⟩ : monicSubmonoid A)).unit

@[simp] theorem variableUnit_val : (variableUnit A : MonicFrac A) =
    algebraMap (Polynomial A) (MonicFrac A) Polynomial.X := IsUnit.unit_spec _

def laurentToMonic : LaurentPolynomial A →+* MonicFrac A :=
  LaurentPolynomial.eval₂ (constant A) (variableUnit A)

@[simp] theorem laurentToMonic_C (a : A) : laurentToMonic A (LaurentPolynomial.C a) =
    constant A a := LaurentPolynomial.eval₂_C _ _ _

@[simp] theorem laurentToMonic_T (i : ℤ) : laurentToMonic A (LaurentPolynomial.T i) =
    ((variableUnit A) ^ i : (MonicFrac A)ˣ) := LaurentPolynomial.eval₂_T _ _ _

variable {A} {B : Type*} [CommRing B]

@[simp] theorem mapCoefficients_inclusion (f : A →+* B) (p : Polynomial A) :
    mapCoefficients f (algebraMap (Polynomial A) (MonicFrac A) p) =
      algebraMap (Polynomial B) (MonicFrac B) (p.map f) := by
  exact IsLocalization.map_eq (M := monicSubmonoid A) (S := MonicFrac A)
    (T := monicSubmonoid B) (Q := MonicFrac B) (g := Polynomial.mapRingHom f)
    (fun _ h => Polynomial.Monic.map f h) p

@[simp] theorem mapCoefficients_constant (f : A →+* B) (a : A) :
    mapCoefficients f (constant A a) = constant B (f a) := by
  simp [constant]

theorem mapCoefficients_variableUnit (f : A →+* B) :
    Units.map (mapCoefficients f).toMonoidHom (variableUnit A) = variableUnit B := by
  apply Units.ext
  simp

theorem laurentToMonic_natural (f : A →+* B) :
    (mapCoefficients f).comp (laurentToMonic A) =
      (laurentToMonic B).comp (AddMonoidAlgebra.mapRingHom ℤ f) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro a
    change mapCoefficients f (laurentToMonic A (LaurentPolynomial.C a)) =
      laurentToMonic B (AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.C a))
    have hc : AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.C a) = LaurentPolynomial.C (f a) :=
      AddMonoidAlgebra.mapRingHom_single f 0 a
    rw [hc, laurentToMonic_C, laurentToMonic_C, mapCoefficients_constant]
  · intro i
    change mapCoefficients f (laurentToMonic A (LaurentPolynomial.T i)) =
      laurentToMonic B (AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.T i))
    rw [laurentToMonic_T]
    have ht : AddMonoidAlgebra.mapRingHom ℤ f (LaurentPolynomial.T i) = LaurentPolynomial.T i := by
      change AddMonoidAlgebra.mapRingHom ℤ f (AddMonoidAlgebra.single i 1) =
        AddMonoidAlgebra.single i 1
      rw [AddMonoidAlgebra.mapRingHom_single, map_one]
    rw [ht, laurentToMonic_T]
    have hh : ((Units.map (mapCoefficients f).toMonoidHom) (variableUnit A ^ i) : MonicFrac B) =
        ((variableUnit B ^ i : (MonicFrac B)ˣ) : MonicFrac B) := by
      rw [map_zpow, mapCoefficients_variableUnit]
    exact hh

section VariableSeparation

variable (K G : Type*) [CommRing K] [AddCommMonoid G]

abbrev CoefficientLaurent := AddMonoidAlgebra K G

def coefficientInclusion : K →+* CoefficientLaurent K G := AddMonoidAlgebra.singleZeroRingHom

def genericToMonic : AddMonoidAlgebra (MonicFrac K) G →+* MonicFrac (CoefficientLaurent K G) :=
  AddMonoidAlgebra.liftNCRingHom
    (mapCoefficients (coefficientInclusion K G))
    ((constant (CoefficientLaurent K G)).toMonoidHom.comp (AddMonoidAlgebra.of K G))
    (fun _ _ => Commute.all _ _)

def separateVariable : LaurentPolynomial (CoefficientLaurent K G) →+*
    AddMonoidAlgebra (MonicFrac K) G :=
  (AddMonoidAlgebra.mapRingHom G (laurentToMonic K)).comp
    AddMonoidAlgebra.commRingEquiv.toRingHom

@[simp] theorem genericToMonic_single (g : G) (a : MonicFrac K) :
    genericToMonic K G (AddMonoidAlgebra.single g a) =
      mapCoefficients (coefficientInclusion K G) a *
        constant (CoefficientLaurent K G) (AddMonoidAlgebra.single g 1) := by
  simp [genericToMonic, AddMonoidAlgebra.of]

@[simp] theorem separateVariable_single (i : ℤ) (g : G) (a : K) :
    separateVariable K G (AddMonoidAlgebra.single i (AddMonoidAlgebra.single g a)) =
      AddMonoidAlgebra.single g (laurentToMonic K (AddMonoidAlgebra.single i a)) := by
  change AddMonoidAlgebra.mapRingHom G (laurentToMonic K)
    (AddMonoidAlgebra.commRingEquiv (AddMonoidAlgebra.single i (AddMonoidAlgebra.single g a))) = _
  rw [AddMonoidAlgebra.commRingEquiv_single_single, AddMonoidAlgebra.mapRingHom_single]

theorem generic_comp_separate :
    (genericToMonic K G).comp (separateVariable K G) =
      laurentToMonic (CoefficientLaurent K G) := by
  apply RingHom.coe_addMonoidHom_injective
  apply AddMonoidAlgebra.addMonoidHom_ext
  intro i b
  have hi :
      ((genericToMonic K G).comp (separateVariable K G)).toAddMonoidHom.comp
          (AddMonoidAlgebra.singleAddHom i) =
      (laurentToMonic (CoefficientLaurent K G)).toAddMonoidHom.comp
          (AddMonoidAlgebra.singleAddHom i) := by
    apply AddMonoidAlgebra.addMonoidHom_ext
    intro g a
    change genericToMonic K G (separateVariable K G
      (AddMonoidAlgebra.single i (AddMonoidAlgebra.single g a))) =
      laurentToMonic (CoefficientLaurent K G)
        (AddMonoidAlgebra.single i (AddMonoidAlgebra.single g a))
    rw [separateVariable_single, genericToMonic_single]
    have hn := DFunLike.congr_fun (laurentToMonic_natural (coefficientInclusion K G))
      (AddMonoidAlgebra.single i a)
    change mapCoefficients (coefficientInclusion K G)
        (laurentToMonic K (AddMonoidAlgebra.single i a)) =
      laurentToMonic (CoefficientLaurent K G)
        (AddMonoidAlgebra.mapRingHom ℤ (coefficientInclusion K G) (AddMonoidAlgebra.single i a)) at hn
    rw [hn, AddMonoidAlgebra.mapRingHom_single]
    rw [LaurentPolynomial.single_eq_C_mul_T, map_mul, laurentToMonic_C,
      LaurentPolynomial.single_eq_C_mul_T, map_mul, laurentToMonic_C]
    have hc : coefficientInclusion K G a * AddMonoidAlgebra.single g 1 =
        AddMonoidAlgebra.single g a := by
      simp [coefficientInclusion, AddMonoidAlgebra.single_mul_single]
    rw [mul_right_comm, ← map_mul, hc]
  exact DFunLike.congr_fun hi b

/-- The lower-dimensional criterion over rational-function coefficients
proves freeness on the actual positive generic chart. -/
theorem generic_image_free [Nontrivial K]
    (hgeneric : IdempotentCriterion (AddMonoidAlgebra (MonicFrac K) G)) {n : ℕ}
    (E : Matrix (Fin n) (Fin n) (LaurentPolynomial (CoefficientLaurent K G)))
    (hE : E * E = E) :
    Module.Free (MonicFrac (CoefficientLaurent K G))
      (LinearMap.range (E.map (laurentToMonic (CoefficientLaurent K G))).mulVecLin) := by
  let : Nontrivial (MonicFrac K) := Function.Injective.nontrivial
    (polynomialInclusion_injective (A := K))
  have hs : E.map (separateVariable K G) * E.map (separateVariable K G) =
      E.map (separateVariable K G) := by rw [← Matrix.map_mul, hE]
  have hf := free_range_map (E.map (separateVariable K G)) hs
    (hgeneric n _ hs) (genericToMonic K G)
  have he : (E.map (separateVariable K G)).map (genericToMonic K G) =
      E.map (laurentToMonic (CoefficientLaurent K G)) := by
    funext i j
    exact DFunLike.congr_fun (generic_comp_separate K G) (E i j)
  rwa [he] at hf

theorem generic_image_free_comp [Nontrivial K]
    (hgeneric : IdempotentCriterion (AddMonoidAlgebra (MonicFrac K) G)) {n : ℕ}
    (E : Matrix (Fin n) (Fin n) (LaurentPolynomial (CoefficientLaurent K G)))
    (hE : E * E = E)
    (f : LaurentPolynomial (CoefficientLaurent K G) →+*
      LaurentPolynomial (CoefficientLaurent K G)) :
    Module.Free (MonicFrac (CoefficientLaurent K G))
      (LinearMap.range ((E.map f).map (laurentToMonic (CoefficientLaurent K G))).mulVecLin) := by
  have hi : E.map f * E.map f = E.map f := by rw [← Matrix.map_mul, hE]
  exact generic_image_free K G hgeneric (E.map f) hi

/-- The same induction hypothesis supplies the opposite generic chart by
the literal Laurent inversion, with no Laurent local-global assumption. -/
theorem opposite_generic_image_free [Nontrivial K]
    (hgeneric : IdempotentCriterion (AddMonoidAlgebra (MonicFrac K) G)) {n : ℕ}
    (E : Matrix (Fin n) (Fin n) (LaurentPolynomial (CoefficientLaurent K G)))
    (hE : E * E = E) :
    Module.Free (MonicFrac (CoefficientLaurent K G))
      (LinearMap.range ((E.map LaurentPolynomial.invert.toRingHom).map
        (laurentToMonic (CoefficientLaurent K G))).mulVecLin) :=
  generic_image_free_comp K G hgeneric E hE LaurentPolynomial.invert.toRingHom

end VariableSeparation

end
end Decoupling.SwanScalarExtension
