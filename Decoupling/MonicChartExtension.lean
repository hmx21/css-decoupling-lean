import Decoupling.LaurentFreeness
import Decoupling.MonicLocalization
import Mathlib.RingTheory.Localization.Free
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# From a principal overlap trivialization to an actual extension

The new module is a concrete kernel inside the product of the original chart
and a free second chart. Its localizations and finite projectivity are proved.
No pre-existing global extension is part of the input.
-/

namespace Decoupling.MonicChartExtension

open LaurentFreeness

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000

section LocalizationModels

attribute [local instance] RingHomInvPair.of_ringEquiv RingHomInvPair.of_ringEquiv_symm

variable {A : Type*} [CommRing A] (S : Submonoid A)
  (B C : Type*) [CommRing B] [CommRing C] [Algebra A B] [Algebra A C]
  [IsLocalization S B] [IsLocalization S C]
  {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module A M] [Module A N]
  [Module B M] [Module C N] [IsScalarTower A B M] [IsScalarTower A C N]

local instance modelRingInvPair :
    RingHomInvPair (IsLocalization.algEquiv S B C).toRingEquiv.toRingHom
      (IsLocalization.algEquiv S B C).toRingEquiv.symm.toRingHom :=
  RingHomInvPair.of_ringEquiv (IsLocalization.algEquiv S B C).toRingEquiv

local instance modelRingInvPairSymm :
    RingHomInvPair (IsLocalization.algEquiv S B C).toRingEquiv.symm.toRingHom
      (IsLocalization.algEquiv S B C).toRingEquiv.toRingHom :=
  RingHomInvPair.of_ringEquiv_symm (IsLocalization.algEquiv S B C).toRingEquiv

/-- An equivalence of localized modules transports the actual localized scalars,
not only the underlying coefficient action. -/
def localizationModelEquiv (e : M ≃ₗ[A] N) :
    LinearEquiv (IsLocalization.algEquiv S B C).toRingEquiv.toRingHom
      (σ' := (IsLocalization.algEquiv S B C).toRingEquiv.symm.toRingHom) M N where
  __ := e.toAddEquiv
  map_smul' c x := by
    obtain ⟨r, s, rfl⟩ := IsLocalization.exists_mk'_eq S c
    change e (IsLocalization.mk' B r s • x) =
      (IsLocalization.algEquiv S B C) (IsLocalization.mk' B r s) • e x
    rw [IsLocalization.algEquiv_mk']
    apply (IsLocalization.map_units C s).smul_left_cancel.mp
    simp only [algebraMap_smul, ← e.map_smul, ← smul_assoc,
      IsLocalization.smul_mk'_self]

include S in
/-- Native freeness is independent of the chosen ring/module models of a localization. -/
theorem free_of_localizationModelEquiv (e : M ≃ₗ[A] N) [Module.Free B M] : Module.Free C N := by
  let φ := (IsLocalization.algEquiv S B C).toRingEquiv
  let : RingHomInvPair φ.toRingHom φ.symm.toRingHom := RingHomInvPair.of_ringEquiv φ
  let : RingHomInvPair φ.symm.toRingHom φ.toRingHom := RingHomInvPair.of_ringEquiv_symm φ
  exact Module.Free.of_equiv (localizationModelEquiv S B C e)

end LocalizationModels

section AssociatedDenominators

variable {A : Type*} [CommRing A] {P : Type*} [AddCommGroup P] [Module A P]
  {a b : A}

/-- Native freeness survives replacing a principal denominator by an associate;
both the module and coefficient localization are transported. -/
theorem free_of_associated (hab : Associated a b)
    [Module.Free (Localization.Away a) (LocalizedModule.Away a P)] :
    Module.Free (Localization.Away b) (LocalizedModule.Away b P) := by
  let : IsLocalization.Away a (Localization.Away b) :=
    IsLocalization.Away.of_associated hab.symm
  let : IsLocalizedModule.Away a
      (LocalizedModule.mkLinearMap (Submonoid.powers b) P) :=
    IsLocalizedModule.Away.of_associated hab.symm
  exact free_of_localizationModelEquiv (Submonoid.powers a)
    (Localization.Away a) (Localization.Away b)
    (IsLocalizedModule.linearEquiv (Submonoid.powers a)
      (LocalizedModule.mkLinearMap (Submonoid.powers a) P)
      (LocalizedModule.mkLinearMap (Submonoid.powers b) P))

end AssociatedDenominators

section PrincipalChart

variable {A : Type*} [CommRing A] (a b : A)
  {P : Type*} [AddCommGroup P] [Module A P]
  [Module (Localization.Away a) P] [IsScalarTower A (Localization.Away a) P]
  (r : ℕ)

abbrev FreeChart := Fin r → Localization.Away b
abbrev Overlap := LocalizedModule.Away a (FreeChart b r)

variable (e : LocalizedModule.Away b P ≃ₗ[A] Overlap a b r)

def leftMap : P →ₗ[A] Overlap a b r :=
  e.toLinearMap.comp (LocalizedModule.mkLinearMap (Submonoid.powers b) P)

abbrev rightMap : FreeChart b r →ₗ[A] Overlap a b r :=
  LocalizedModule.mkLinearMap (Submonoid.powers a) (FreeChart b r)

instance leftMap_localized : IsLocalizedModule.Away b (leftMap a b r e) :=
  IsLocalizedModule.of_linearEquiv (Submonoid.powers b)
    (LocalizedModule.mkLinearMap (Submonoid.powers b) P) e

/-- This is the constructed extension; the original chart and free chart
are actual factors, and compatibility is an explicit linear kernel. -/
abbrev Extension := compatibleSections (A := A) (M₁ := P) (M₂ := FreeChart b r)
  (M₁₂ := Overlap a b r) (leftMap a b r e) (rightMap a b r)

/-- Localization of the constructed module recovers the original module. -/
def extensionEquiv : LocalizedModule.Away a (Extension a b r e) ≃ₗ[Localization.Away a] P :=
  firstChartLocalizedEquiv (A := A) (M₁ := P) (M₂ := FreeChart b r)
    (M₁₂ := Overlap a b r) (leftMap a b r e) (rightMap a b r) a

/-- On the other chart the constructed module has the supplied finite rank. -/
def extensionFreeChartEquiv :
    LocalizedModule.Away b (Extension a b r e) ≃ₗ[Localization.Away b] FreeChart b r :=
  secondChartLocalizedEquiv (A := A) (M₁ := P) (M₂ := FreeChart b r)
    (M₁₂ := Overlap a b r) (leftMap a b r e) (rightMap a b r) b

/-- The construction produces a finite projective module from the actual
principal-overlap trivialization and the complementary-cover equation. -/
theorem extension_finite_projective (hab : IsCoprime a b)
    [Module.Finite (Localization.Away a) P] [Module.Projective (Localization.Away a) P] :
    Module.Finite A (Extension a b r e) ∧ Module.Projective A (Extension a b r e) :=
  glued_finite_projective (A := A) (M₁ := P) (M₂ := FreeChart b r)
    (M₁₂ := Overlap a b r) (leftMap a b r e) (rightMap a b r) a b hab

end PrincipalChart

section NativeOverlap

variable {A : Type*} [CommRing A] (a b : A)
  {P : Type*} [AddCommGroup P] [Module A P]
  [Module (Localization.Away a) P] [IsScalarTower A (Localization.Away a) P]
  (D : Type*) [CommRing D] [Algebra A D]
  [Algebra (Localization.Away a) D] [IsScalarTower A (Localization.Away a) D]
  [Algebra (Localization.Away b) D] [IsScalarTower A (Localization.Away b) D]
  [IsLocalization.Away (algebraMap A (Localization.Away a) b) D]
  [IsLocalization.Away (algebraMap A (Localization.Away b) a) D]

/-- The actual localization of the original module on the overlap. -/
abbrev OriginalOverlap :=
  LocalizedModule.Away (algebraMap A (Localization.Away a) b) P

attribute [local instance] LocalizedModule.moduleOfIsLocalization

instance originalOverlap_scalarTower : IsScalarTower A D (OriginalOverlap a b (P := P)) :=
  IsScalarTower.of_algebraMap_smul fun r m => by
    rw [IsScalarTower.algebraMap_apply A (Localization.Away a) D,
      algebraMap_smul, algebraMap_smul]

def originalOverlapMap : P →ₗ[A] OriginalOverlap a b (P := P) :=
  (LocalizedModule.mkLinearMap
    (Submonoid.powers (algebraMap A (Localization.Away a) b)) P).restrictScalars A

instance originalOverlapMap_localized :
    IsLocalizedModule.Away b (originalOverlapMap a b (P := P)) :=
  IsLocalizedModule.restrictScalars_powers b
    (LocalizedModule.mkLinearMap
      (Submonoid.powers (algebraMap A (Localization.Away a) b)) P)

/-- Coefficients of the free opposite chart map to the actual common ring. -/
def freeOverlapMap (r : ℕ) : FreeChart b r →ₗ[A] (Fin r → D) :=
  (Finsupp.linearEquivFunOnFinite A D (Fin r)).toLinearMap.comp
    (((Finsupp.mapRange.linearMap
      (Algebra.linearMap (Localization.Away b) D)).restrictScalars A).comp
        (Finsupp.linearEquivFunOnFinite A (Localization.Away b) (Fin r)).symm.toLinearMap)

instance freeOverlapMap_localized (r : ℕ) :
    IsLocalizedModule.Away a (freeOverlapMap b D r) := by
  let f := (Finsupp.mapRange.linearMap (α := Fin r)
    (Algebra.linearMap (Localization.Away b) D)).restrictScalars A
  let e₁ := Finsupp.linearEquivFunOnFinite A (Localization.Away b) (Fin r)
  let e₂ := Finsupp.linearEquivFunOnFinite A D (Fin r)
  have : IsLocalizedModule.Away a f :=
    IsLocalizedModule.restrictScalars_powers a
      (Finsupp.mapRange.linearMap (Algebra.linearMap (Localization.Away b) D))
  have : IsLocalizedModule.Away a (f.comp e₁.symm.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (Submonoid.powers a) f e₁.symm
  exact IsLocalizedModule.of_linearEquiv (Submonoid.powers a) _ e₂

/-- A basis over the canonical localization transports to any actual model
of the same overlap ring, by the localization's algebra equivalence. -/
def overlapBasisOfCanonical {r : ℕ}
    (basis : Module.Basis (Fin r)
      (Localization.Away (algebraMap A (Localization.Away a) b))
      (OriginalOverlap a b (P := P))) :
    Module.Basis (Fin r) D (OriginalOverlap a b (P := P)) := by
  let φ := IsLocalization.algEquiv
    (Submonoid.powers (algebraMap A (Localization.Away a) b))
    (Localization.Away (algebraMap A (Localization.Away a) b)) D
  let e := (basis.equivFun.restrictScalars (Localization.Away a)).trans
    (LinearEquiv.piCongrRight (fun _ : Fin r => φ.toLinearEquiv))
  exact Module.Basis.ofEquivFun (e.extendScalarsOfIsLocalization
    (Submonoid.powers (algebraMap A (Localization.Away a) b)) D)

/-- A native basis after localization constructs the chart identification.
There is no supplied gluing map or abstract desired extension in this input. -/
def overlapEquivOfBasis {r : ℕ}
    (basis : Module.Basis (Fin r) D (OriginalOverlap a b (P := P))) :
    LocalizedModule.Away b P ≃ₗ[A] Overlap a b r :=
  (IsLocalizedModule.iso (Submonoid.powers b) (originalOverlapMap a b (P := P))).trans
    ((basis.equivFun.restrictScalars A).trans
      (IsLocalizedModule.iso (Submonoid.powers a) (freeOverlapMap b D r)).symm)

/-- Swan's extension module, constructed from an actual overlap basis. -/
abbrev ExtensionOfBasis {r : ℕ}
    (basis : Module.Basis (Fin r) D (OriginalOverlap a b (P := P))) :=
  Extension a b r (overlapEquivOfBasis a b D basis)

def extensionOfBasisEquiv {r : ℕ}
    (basis : Module.Basis (Fin r) D (OriginalOverlap a b (P := P))) :
    LocalizedModule.Away a (ExtensionOfBasis a b D basis) ≃ₗ[Localization.Away a] P :=
  extensionEquiv a b r (overlapEquivOfBasis a b D basis)

theorem extensionOfBasis_finite_projective {r : ℕ}
    (basis : Module.Basis (Fin r) D (OriginalOverlap a b (P := P)))
    (hab : IsCoprime a b)
    [Module.Finite (Localization.Away a) P] [Module.Projective (Localization.Away a) P] :
    Module.Finite A (ExtensionOfBasis a b D basis) ∧
      Module.Projective A (ExtensionOfBasis a b D basis) :=
  extension_finite_projective a b r (overlapEquivOfBasis a b D basis) hab

end NativeOverlap

section CanonicalNativeExtension

open scoped TensorProduct
attribute [local instance] Algebra.TensorProduct.rightAlgebra
  LocalizedModule.moduleOfIsLocalization

variable {A : Type*} [CommRing A] (a b : A)
  {P : Type*} [AddCommGroup P] [Module A P]
  [Module (Localization.Away a) P] [IsScalarTower A (Localization.Away a) P]
  [Module.Finite (Localization.Away a) P]

/-- A concrete common localization of the two charts. -/
abbrev IntersectionRing := Localization.Away a ⊗[A] Localization.Away b
abbrev PrincipalRing := Localization.Away (algebraMap A (Localization.Away a) b)

variable [Nontrivial (PrincipalRing a b)]
  [Module.Free (PrincipalRing a b) (OriginalOverlap a b (P := P))]

/-- A native freeness instance constructs an overlap basis over the concrete
common ring; no overlap identification is supplied. -/
def nativeOverlapBasis :
    Module.Basis (Fin (Module.finrank (PrincipalRing a b) (OriginalOverlap a b (P := P))))
      (IntersectionRing a b) (OriginalOverlap a b (P := P)) := by
  letI : Module.Finite (PrincipalRing a b) (OriginalOverlap a b (P := P)) :=
    Module.Finite.of_isLocalizedModule
      (Submonoid.powers (algebraMap A (Localization.Away a) b))
      (Rₚ := PrincipalRing a b)
      (LocalizedModule.mkLinearMap
        (Submonoid.powers (algebraMap A (Localization.Away a) b)) P)
  exact overlapBasisOfCanonical a b (IntersectionRing a b)
    (Module.finBasis (PrincipalRing a b) (OriginalOverlap a b (P := P)))

/-- The explicit extension constructed solely from principal localized freeness. -/
abbrev NativeExtension :=
  ExtensionOfBasis a b (IntersectionRing a b) (nativeOverlapBasis a b (P := P))

def nativeExtensionEquiv :
    LocalizedModule.Away a (NativeExtension a b (P := P)) ≃ₗ[Localization.Away a] P :=
  extensionOfBasisEquiv a b (IntersectionRing a b) (nativeOverlapBasis a b (P := P))

/-- Finite projectivity of the original Laurent chart extends across its
complementary affine chart whenever the principal overlap is actually free. -/
theorem nativeExtension_finite_projective (hab : IsCoprime a b)
    [Module.Projective (Localization.Away a) P] :
    Module.Finite A (NativeExtension a b (P := P)) ∧
      Module.Projective A (NativeExtension a b (P := P)) :=
  extensionOfBasis_finite_projective a b (IntersectionRing a b)
    (nativeOverlapBasis a b (P := P)) hab

end CanonicalNativeExtension

section FiniteDenominator

open Polynomial LaurentPolynomial

variable (A : Type*) [CommRing A]

/-- Monic polynomial denominators viewed inside the actual Laurent ring. -/
def monicImage : Submonoid (LaurentPolynomial A) :=
  (MonicLocalization.monicSubmonoid A).map Polynomial.toLaurent

abbrev MonicLaurentFrac := Localization (monicImage A)

instance monicLaurentFrac_nontrivial [Nontrivial A] : Nontrivial (MonicLaurentFrac A) :=
  (IsLocalization.toLocalizationMap (monicImage A) (MonicLaurentFrac A)).nontrivial (by
    rintro ⟨f, hf, hfzero⟩
    apply hf.ne_zero
    exact Polynomial.toLaurent_injective (hfzero.trans (map_zero Polynomial.toLaurent).symm))


variable {P : Type*} [AddCommGroup P] [Module (LaurentPolynomial A) P]
  [Module.FinitePresentation (LaurentPolynomial A) P]
  [Nontrivial A]
  [Module.Free (MonicLaurentFrac A) (LocalizedModule (monicImage A) P)]

/-- A native free basis after inversion of all monic polynomials already exists
after inversion of one concrete monic polynomial. The finite rank is preserved. -/
theorem exists_monic_free :
    ∃ f : A[X], f.Monic ∧
      Module.Free (Localization.Away (toLaurent f)) (LocalizedModule.Away (toLaurent f) P) ∧
      Module.finrank (Localization.Away (toLaurent f)) (LocalizedModule.Away (toLaurent f) P) =
        Module.finrank (MonicLaurentFrac A) (LocalizedModule (monicImage A) P) := by
  obtain ⟨r, hr, hfree, hrank⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers (monicImage A)
      (LocalizedModule.mkLinearMap (monicImage A) P) (MonicLaurentFrac A)
  obtain ⟨f, hf, rfl⟩ := hr
  exact ⟨f, hf, hfree, hrank⟩

end FiniteDenominator

end
end Decoupling.MonicChartExtension
