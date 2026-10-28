import Decoupling.SwanExtension
import Decoupling.MonicBaseChange
import Decoupling.SwanChartModels
import Mathlib.LinearAlgebra.TensorProduct.Free

/-!
# The Swan induction step from the two actual generic charts

The opposite generic chart supplies the constructed polynomial extension.
The positive generic chart and the proved polynomial monic-inversion theorem
then produce its free basis and hence the original Laurent module's basis.
-/

namespace Decoupling.SwanStep

open MonicLocalization ProjectiveFreeness SwanExtension
open scoped TensorProduct

noncomputable section

variable (A : Type*) [CommRing A] [IsDomain A]
  [Algebra (Laurent A) (MonicFrac A)]
  [IsScalarTower (Polynomial A) (Laurent A) (MonicFrac A)]
  (P : Type*) [AddCommGroup P] [Module (Polynomial A) P]
  [Module (Laurent A) P] [IsScalarTower (Polynomial A) (Laurent A) P]
  [Module.Finite (Laurent A) P] [Module.Projective (Laurent A) P]

omit [Module (Polynomial A) P] [IsScalarTower (Polynomial A) (Laurent A) P]
  [Module.Finite (Laurent A) P] [Module.Projective (Laurent A) P] in
/-- A constructed extension becomes free from the positive generic chart.
All module structures and tensor products are the native ones. -/
theorem free_of_extension (Q : Extension A P) (hA : IdempotentCriterion A)
    (hpos : Module.Free (MonicFrac A) (MonicFrac A ⊗[Laurent A] P)) :
    Module.Free (Laurent A) P := by
  let := Q.addCommGroup
  let := Q.module
  let := Q.finite
  let := Q.projective
  let e : (Laurent A ⊗[Polynomial A] Q.carrier) ≃ₗ[Laurent A] P :=
    (LocalizedModule.equivTensorProduct (Submonoid.powers (Polynomial.X : Polynomial A))
      Q.carrier).symm.trans Q.localizationEquiv
  let e' := (TensorProduct.AlgebraTensorModule.cancelBaseChange (Polynomial A) (Laurent A)
    (MonicFrac A) (MonicFrac A) Q.carrier).symm.trans
    (e.baseChange (Laurent A) (MonicFrac A) _ _)
  let := hpos
  have hQpos : Module.Free (MonicFrac A) (MonicFrac A ⊗[Polynomial A] Q.carrier) :=
    Module.Free.of_equiv e'.symm
  let := MonicBaseChange.native_free_of_monic_baseChange hA hQpos
  have : Module.Free (Laurent A) (Laurent A ⊗[Polynomial A] Q.carrier) := inferInstance
  exact Module.Free.of_equiv e

omit [Module (Polynomial A) P] [IsScalarTower (Polynomial A) (Laurent A) P] in
/-- The two-half criterion needed for the Laurent variable induction.
The extension is obtained from negative-chart freeness, not supplied. -/
theorem free_of_two_generic_charts (hA : IdempotentCriterion A)
    [Module.Free (NegativeGeneric A) (LocalizedModule (negativeMonic A) P)]
    (hpos : Module.Free (MonicFrac A) (MonicFrac A ⊗[Laurent A] P)) :
    Module.Free (Laurent A) P := by
  let : Module (Polynomial A) P := Module.compHom P (algebraMap (Polynomial A) (Laurent A))
  let : IsScalarTower (Polynomial A) (Laurent A) P :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact free_of_extension A P (of_negative_free A P) hA hpos

end

noncomputable section Canonical

variable (A : Type*) [CommRing A] [IsDomain A]
  (P : Type*) [AddCommGroup P] [Module (Laurent A) P]
  [Module.Finite (Laurent A) P] [Module.Projective (Laurent A) P]

/-- The same theorem with the actual positive Laurent-to-monic scalar map
fixed internally, so callers need not build scalar-tower instances. -/
theorem canonical_free_of_two_generic_charts (hA : IdempotentCriterion A)
    [Module.Free (NegativeGeneric A) (LocalizedModule (negativeMonic A) P)]
    (hpos : letI := SwanChartModels.positiveAlgebra A
      Module.Free (MonicFrac A) (MonicFrac A ⊗[Laurent A] P)) :
    Module.Free (Laurent A) P := by
  let := SwanChartModels.positiveAlgebra A
  let := SwanChartModels.positiveTower A
  exact free_of_two_generic_charts A P hA hpos

end Canonical

noncomputable section Idempotents

variable (A : Type*) [CommRing A] [IsDomain A]

/-- Matrix-image entry point to the actual two-chart theorem. -/
theorem canonical_idempotent_free {n : ℕ}
    (E : Matrix (Fin n) (Fin n) (Laurent A)) (hE : E * E = E)
    (hA : IdempotentCriterion A)
    [Module.Free (NegativeGeneric A) (LocalizedModule (negativeMonic A)
      (IdempotentBaseChange.Image E))]
    (hpos : Module.Free (MonicFrac A)
      (LinearMap.range (E.map (SwanChartModels.positiveMap A)).mulVecLin)) :
    Module.Free (Laurent A) (IdempotentBaseChange.Image E) := by
  let := IdempotentPresentation.projective_range E hE
  exact canonical_free_of_two_generic_charts A (IdempotentBaseChange.Image E) hA
    (SwanChartModels.positive_free_of_image_free A E hE hpos)

end Idempotents
end Decoupling.SwanStep
