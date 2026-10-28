import Decoupling.LocalHorrocks
import Decoupling.IdempotentBaseChange

/-!
# Native module form of the local Horrocks theorem

The matrix theorem is transported through an actual idempotent presentation
and an actual scalar-extension equivalence. Both projectivity and freeness
are mathlib's native module properties.
-/

namespace Decoupling.HorrocksNative

open MonicLocalization Polynomial TensorProduct
open scoped TensorProduct

noncomputable section

variable {A P : Type*} [CommRing A] [IsLocalRing A]
  [AddCommGroup P] [Module A[X] P]

/-- A finite projective over a local coefficient polynomial ring is free
if its scalar extension to the monic localization is free. -/
theorem free_of_monic_baseChange [Module.Finite A[X] P] [Module.Projective A[X] P]
    (hf : Module.Free (MonicFrac A) (MonicFrac A ⊗[A[X]] P)) :
    Module.Free A[X] P := by
  obtain ⟨n, E, hE, ⟨e⟩⟩ := IdempotentPresentation.exists_idempotent (A := A[X]) (P := P)
  let e' := (e.baseChange A[X] (MonicFrac A) P (LinearMap.range E.mulVecLin)).trans
    (IdempotentBaseChange.imageEquiv (B := MonicFrac A) E hE)
  let := hf
  have hloc : Module.Free (MonicFrac A)
      (LinearMap.range (E.map (algebraMap A[X] (MonicFrac A))).mulVecLin) :=
    Module.Free.of_equiv e'
  let := LocalHorrocks.free_range_of_monic_free E hE hloc
  exact Module.Free.of_equiv e.symm

/-- The same theorem for any genuine model of monic module localization. -/
theorem free_of_monic_localization [Module.Finite A[X] P] [Module.Projective A[X] P]
    {Q : Type*} [AddCommGroup Q] [Module A[X] Q] [Module (MonicFrac A) Q]
    [IsScalarTower A[X] (MonicFrac A) Q] (f : P →ₗ[A[X]] Q)
    [IsLocalizedModule (monicSubmonoid A) f] [Module.Free (MonicFrac A) Q] :
    Module.Free A[X] P := by
  have hf : Module.Free (MonicFrac A) (MonicFrac A ⊗[A[X]] P) :=
    Module.Free.of_equiv ((IsLocalizedModule.isBaseChange (monicSubmonoid A)
      (MonicFrac A) f).equiv.symm)
  exact free_of_monic_baseChange hf

end

end Decoupling.HorrocksNative
