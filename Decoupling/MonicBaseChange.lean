import Decoupling.SwanScalarExtension
import Decoupling.PolynomialLocalPatch
import Decoupling.LocalHorrocks
import Decoupling.IdempotentBaseChange

/-! # Genuine scalar extension of monic-localization freeness -/

namespace Decoupling.MonicBaseChange

open MonicLocalization ProjectiveFreeness SwanScalarExtension

noncomputable section

variable {A B : Type*} [CommRing A] [CommRing B] [Nontrivial A]
  {n : ℕ} (E : Matrix (Fin n) (Fin n) (Polynomial A)) (hE : E * E = E)

include hE

/-- Freeness over A(x) is preserved after any coefficient change A→B,
using the actual map of monic localizations and native matrix-image modules. -/
theorem free_after_coefficient_change
    (hf : Module.Free (MonicFrac A) (LinearMap.range
      (E.map (algebraMap (Polynomial A) (MonicFrac A))).mulVecLin)) (f : A →+* B) :
    Module.Free (MonicFrac B) (LinearMap.range
      ((E.map (Polynomial.mapRingHom f)).map
        (algebraMap (Polynomial B) (MonicFrac B))).mulVecLin) := by
  let : Nontrivial (MonicFrac A) := Function.Injective.nontrivial
    (polynomialInclusion_injective (A := A))
  have hi : E.map (algebraMap (Polynomial A) (MonicFrac A)) *
      E.map (algebraMap (Polynomial A) (MonicFrac A)) =
      E.map (algebraMap (Polynomial A) (MonicFrac A)) := by
    rw [← Matrix.map_mul, hE]
  have h := free_range_map _ hi hf (mapCoefficients f)
  have he : (E.map (algebraMap (Polynomial A) (MonicFrac A))).map (mapCoefficients f) =
      (E.map (Polynomial.mapRingHom f)).map (algebraMap (Polynomial B) (MonicFrac B)) := by
    funext i j
    exact mapCoefficients_inclusion f (E i j)
  rwa [he] at h

section LocalGlobal

variable [IsDomain A]

omit [Nontrivial A] in
/-- Monic inversion over a domain whose finite projectives are free.
Local Horrocks and polynomial patching are both proved dependencies. -/
theorem free_of_monic_free
    (hA : IdempotentCriterion A)
    (hf : Module.Free (MonicFrac A) (LinearMap.range
      (E.map (algebraMap (Polynomial A) (MonicFrac A))).mulVecLin)) :
    Module.Free (Polynomial A) (LinearMap.range E.mulVecLin) := by
  apply PolynomialPatching.free_of_local_free E hE
  · intro m hm
    let f := algebraMap A (Localization.AtPrime m)
    have hi : E.map (Polynomial.mapRingHom f) * E.map (Polynomial.mapRingHom f) =
        E.map (Polynomial.mapRingHom f) := by rw [← Matrix.map_mul, hE]
    exact LocalHorrocks.free_range_of_monic_free (E.map (Polynomial.mapRingHom f)) hi
      (free_after_coefficient_change E hE hf f)
  · apply hA
    rw [← Matrix.map_mul, hE]

end LocalGlobal

end

noncomputable section Native

open scoped TensorProduct

variable {A P : Type*} [CommRing A] [IsDomain A]
  [AddCommGroup P] [Module (Polynomial A) P]

/-- Native finite projectives over the polynomial ring satisfy the same
proved monic-inversion theorem, via their actual idempotent presentation. -/
theorem native_free_of_monic_baseChange
    [Module.Finite (Polynomial A) P] [Module.Projective (Polynomial A) P]
    (hA : IdempotentCriterion A)
    (hf : Module.Free (MonicFrac A) (MonicFrac A ⊗[Polynomial A] P)) :
    Module.Free (Polynomial A) P := by
  obtain ⟨n, E, hE, ⟨e⟩⟩ := IdempotentPresentation.exists_idempotent
    (A := Polynomial A) (P := P)
  let e' := (e.baseChange (Polynomial A) (MonicFrac A) P (LinearMap.range E.mulVecLin)).trans
    (IdempotentBaseChange.imageEquiv (B := MonicFrac A) E hE)
  let := hf
  have hloc : Module.Free (MonicFrac A)
      (LinearMap.range (E.map (algebraMap (Polynomial A) (MonicFrac A))).mulVecLin) :=
    Module.Free.of_equiv e'
  let := free_of_monic_free E hE hA hloc
  exact Module.Free.of_equiv e.symm

end Native
end Decoupling.MonicBaseChange
