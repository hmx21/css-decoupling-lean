import Decoupling.MonicChartExtension

/-!
# Swan's opposite-chart extension

The Laurent ring is represented by the canonical localization `A[X]_X`,
with its explicit equivalence to `LaurentPolynomial A`.  Native freeness after
inverting the negative-variable monic polynomials produces an actual finite
projective module over `A[X]` whose localization is the given Laurent module.
This is the free-overlap case of Swan (1978), Lemma 1.3.  The gluing module and
its finite projectivity are constructed, rather than assumed.
-/

namespace Decoupling.SwanExtension

open Polynomial LaurentPolynomial MonicChartExtension

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u v

variable (A : Type u) [CommRing A]

abbrev Laurent := Localization.Away (X : A[X])

/-- The canonical Laurent model and the group-algebra Laurent model agree. -/
def laurentEquiv : Laurent A ≃ₐ[A[X]] LaurentPolynomial A :=
  IsLocalization.algEquiv (Submonoid.powers (X : A[X])) _ _

/-- Polynomial evaluation in the inverse Laurent variable, in the canonical model. -/
def negativePolynomial : A[X] →+* Laurent A :=
  (laurentEquiv A).symm.toRingHom.comp
    (LaurentPolynomial.invert.toRingHom.comp Polynomial.toLaurent)

/-- The genuine submonoid of monic polynomials in the inverse variable. -/
def negativeMonic : Submonoid (Laurent A) :=
  (MonicLocalization.monicSubmonoid A).map (negativePolynomial A)

abbrev NegativeGeneric := Localization (negativeMonic A)

@[simp]
theorem laurentEquiv_algebraMap (f : A[X]) :
    laurentEquiv A (algebraMap A[X] (Laurent A) f) = toLaurent f :=
  (laurentEquiv A).commutes f

@[simp]
theorem laurentEquiv_negative (f : A[X]) :
    laurentEquiv A (negativePolynomial A f) = invert (toLaurent f) :=
  (laurentEquiv A).apply_symm_apply _

theorem negative_reverse_associated (f : A[X]) :
    Associated (negativePolynomial A f) (algebraMap A[X] (Laurent A) f.reverse) := by
  have h : Associated (invert (toLaurent f)) (toLaurent f.reverse) := by
    rw [toLaurent_reverse]
    exact associated_mul_unit_right _ _ (isUnit_T _)
  have hm := h.map (laurentEquiv A).symm.toRingHom
  change Associated (negativePolynomial A f) ((laurentEquiv A).symm (toLaurent f.reverse)) at hm
  simpa only [← laurentEquiv_algebraMap A f.reverse, AlgEquiv.symm_apply_apply] using hm

instance negativeGeneric_nontrivial [Nontrivial A] : Nontrivial (NegativeGeneric A) :=
  (IsLocalization.toLocalizationMap (negativeMonic A) (NegativeGeneric A)).nontrivial (by
    rintro ⟨f, hf, hzero⟩
    have h := congrArg (laurentEquiv A) hzero
    simp only [laurentEquiv_negative, map_zero] at h
    have hz : toLaurent f = 0 := LaurentPolynomial.invert.injective (by simpa using h)
    exact hf.ne_zero (Polynomial.toLaurent_injective (by simpa using hz)))

section Domain

variable [IsDomain A]

/-- The complementary principal overlap is nonzero: the reversed monic
polynomial has constant coefficient one. -/
theorem principal_nontrivial {f : A[X]} (hf : f.Monic) :
    Nontrivial (PrincipalRing (X : A[X]) f.reverse) := by
  have hg : f.reverse ≠ 0 := by
    intro h
    have hc := congrArg (fun p : A[X] => p.coeff 0) h
    rw [LaurentFreeness.reverse_monic_constant hf] at hc
    simp at hc
  have hm : algebraMap A[X] (Laurent A) f.reverse ≠ 0 := by
    simpa only [map_zero] using (IsLocalization.injective (Laurent A)
      (powers_le_nonZeroDivisors_of_noZeroDivisors Polynomial.X_ne_zero)).ne hg
  exact (IsLocalization.toLocalizationMap
    (Submonoid.powers (algebraMap A[X] (Laurent A) f.reverse))
    (PrincipalRing (X : A[X]) f.reverse)).nontrivial
      (by
        rintro ⟨n, hn⟩
        exact (pow_ne_zero n hm) hn)

variable (P : Type v) [AddCommGroup P] [Module A[X] P]
  [Module (Laurent A) P] [IsScalarTower A[X] (Laurent A) P]
  [Module.Finite (Laurent A) P] [Module.Projective (Laurent A) P]

omit [Module A[X] P] [IsScalarTower A[X] (Laurent A) P] in
/-- Finite generation of a localized basis gives one actual negative monic
principal overlap on which the module is free. -/
theorem exists_negative_principal_free
    [Module.Free (NegativeGeneric A) (LocalizedModule (negativeMonic A) P)] :
    ∃ f : A[X], f.Monic ∧
      Module.Free (PrincipalRing (X : A[X]) f.reverse)
        (OriginalOverlap (X : A[X]) f.reverse (P := P)) := by
  let : Module.FinitePresentation (Laurent A) P := Module.finitePresentation_of_projective _ _
  obtain ⟨r, hr, hfree, _⟩ :=
    Module.FinitePresentation.exists_free_localizedModule_powers (negativeMonic A)
      (LocalizedModule.mkLinearMap (negativeMonic A) P) (NegativeGeneric A)
  obtain ⟨f, hf, rfl⟩ := hr
  let : Module.Free (Localization.Away (negativePolynomial A f))
      (LocalizedModule.Away (negativePolynomial A f) P) := hfree
  exact ⟨f, hf, free_of_associated (P := P) (negative_reverse_associated A f)⟩

/-- A finite projective polynomial extension, together with its genuine
localization equivalence to the original Laurent module. -/
structure Extension where
  carrier : Type (max u v)
  [addCommGroup : AddCommGroup carrier]
  [module : Module A[X] carrier]
  [finite : Module.Finite A[X] carrier]
  [projective : Module.Projective A[X] carrier]
  localizationEquiv : LocalizedModule.Away (X : A[X]) carrier ≃ₗ[Laurent A] P

attribute [instance] Extension.addCommGroup Extension.module Extension.finite Extension.projective

omit [IsDomain A] [Module A[X] P] [IsScalarTower A[X] (Laurent A) P]
  [Module.Finite (Laurent A) P] [Module.Projective (Laurent A) P] in
/-- A free polynomial extension makes the original Laurent module free. -/
theorem Extension.free_of_free (e : Extension A P) [Module.Free A[X] e.carrier] :
    Module.Free (Laurent A) P := by
  let : Module.Free (Laurent A) (LocalizedModule.Away (X : A[X]) e.carrier) :=
    Module.Free.of_basis ((Module.Free.chooseBasis A[X] e.carrier).ofIsLocalizedModule
      (Laurent A) (Submonoid.powers (X : A[X]))
      (LocalizedModule.mkLinearMap (Submonoid.powers (X : A[X])) e.carrier))
  exact Module.Free.of_equiv e.localizationEquiv

/-- Swan's extension is obtained from a native monic-localization basis.
No extension module, gluing map, or free principal chart is assumed. -/
def of_negative_free
    [Module.Free (NegativeGeneric A) (LocalizedModule (negativeMonic A) P)] :
    Extension A P := by
  let f := Classical.choose (exists_negative_principal_free A P)
  have hf := (Classical.choose_spec (exists_negative_principal_free A P)).1
  have hfree := (Classical.choose_spec (exists_negative_principal_free A P)).2
  letI : Nontrivial (PrincipalRing (X : A[X]) f.reverse) := principal_nontrivial A hf
  letI := hfree
  let Q := NativeExtension (X : A[X]) f.reverse (P := P)
  have hQ := nativeExtension_finite_projective (X : A[X]) f.reverse (P := P)
    (LaurentFreeness.reverse_monic_coprime hf)
  exact {
    carrier := Q
    finite := hQ.1
    projective := hQ.2
    localizationEquiv := nativeExtensionEquiv (X : A[X]) f.reverse (P := P) }

end Domain
end
end Decoupling.SwanExtension
