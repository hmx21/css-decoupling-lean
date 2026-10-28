import Decoupling.SwanStep
import Decoupling.SwanChartModels
import Decoupling.LaurentVariables
import Decoupling.MonicResidue
import Decoupling.Laurent
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Field.ZMod

/-!
# Laurent projective freeness over a field

Induction on the number of Laurent variables uses the actual rational-function
field for the two generic charts, the constructed Swan extension, local
Horrocks, and the proved polynomial local-global theorem. All freeness
predicates are mathlib's native ones.
-/

namespace Decoupling.SwanInduction

open MonicLocalization ProjectiveFreeness SwanExtension SwanScalarExtension
open scoped TensorProduct

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

universe u

theorem laurent_criterion_of_lower (K G : Type*) [Field K] [AddCommMonoid G]
    [IsDomain (CoefficientLaurent K G)]
    (hA : IdempotentCriterion (CoefficientLaurent K G))
    (hgeneric : IdempotentCriterion (AddMonoidAlgebra (MonicFrac K) G)) :
    IdempotentCriterion (LaurentPolynomial (CoefficientLaurent K G)) := by
  intro n E hE
  let A := CoefficientLaurent K G
  let EC := E.map (laurentEquiv A).symm.toRingHom
  have hEC : EC * EC = EC := by
    dsimp only [EC]
    rw [← Matrix.map_mul, hE]
  let P := IdempotentBaseChange.Image EC
  let : Module.Free (NegativeGeneric A) (LocalizedModule (negativeMonic A) P) :=
    SwanChartModels.negative_free_of_lower K G hgeneric E hE
  have hpos : Module.Free (MonicFrac A)
      (LinearMap.range (EC.map (SwanChartModels.positiveMap A)).mulVecLin) := by
    have he : EC.map (SwanChartModels.positiveMap A) = E.map (laurentToMonic A) := by
      funext i j
      change laurentToMonic A (laurentEquiv A ((laurentEquiv A).symm (E i j))) = _
      rw [AlgEquiv.apply_symm_apply]
      rfl
    rw [he]
    exact generic_image_free K G hgeneric E hE
  have hf : Module.Free (Laurent A) P := SwanStep.canonical_idempotent_free A EC hEC hA hpos
  let : Nontrivial (Laurent A) := Function.Injective.nontrivial (laurentEquiv A).symm.injective
  have h := free_range_map EC hEC hf (laurentEquiv A).toRingHom
  have he : EC.map (laurentEquiv A).toRingHom = E := by
    funext i j
    exact (laurentEquiv A).apply_symm_apply (E i j)
  rwa [he] at h

/-- Every idempotent image over every finite-variable Laurent ring over a
field is a native free module. The field may vary at each induction step. -/
theorem criterion (n : ℕ) : ∀ (K : Type u) [Field K],
    IdempotentCriterion (LaurentVariables.Ring K n) := by
  induction n with
  | zero =>
    intro K _
    exact LaurentVariables.zero_criterion K
  | succ n ih =>
    intro K _
    have h := laurent_criterion_of_lower K (Fin n → ℤ) (ih K) (ih (MonicFrac K))
    exact criterion_of_ringEquiv (LaurentVariables.successorEquiv K n).symm h

/-- The native Swan freeness statement for the manuscript's actual ring. -/
theorem paperRing_free (P : Type) [AddCommGroup P] [Module R P]
    [Module.Finite R P] [Module.Projective R P] : Module.Free R P :=
  (criterion_iff_native.mp (criterion 3 (ZMod 2))) P

end
end Decoupling.SwanInduction
