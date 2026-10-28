import Decoupling.Horrocks
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.LocalRing.ResidueField.Basic
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Residue-field lifting for the monic localization

The constructions here use the actual monic localization and native units,
fields and matrices. They implement the lifting step of Dicks,
arXiv:2112.02272v1, Lemma 3(iii), used in the local Horrocks proof.
-/

namespace Decoupling.MonicResidue

open MonicLocalization Polynomial Matrix

noncomputable section

section Field

variable (K : Type*) [Field K]

/-- Over a field, localizing at monics already gives the full fraction ring. -/
instance monicFrac_isFractionRing : IsFractionRing K[X] (MonicFrac K) :=
  IsLocalization.of_le_of_exists_dvd (monicSubmonoid K) (nonZeroDivisors K[X])
    (fun _ h => mem_nonZeroDivisors_iff_ne_zero.mpr h.ne_zero) (by
      intro p hp
      have hp0 := mem_nonZeroDivisors_iff_ne_zero.mp hp
      exact ⟨p * C p.leadingCoeff⁻¹, monic_mul_leadingCoeff_inv hp0,
        ⟨C p.leadingCoeff⁻¹, rfl⟩⟩)

/-- The field structure is inherited from the genuine fraction-ring property. -/
instance monicFrac_field : Field (MonicFrac K) := IsFractionRing.toField K[X]

end Field

section MatrixLift

variable {C K : Type*} [CommRing C] [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A surjection to a field that lifts scalar units also lifts every
invertible finite matrix. The proof uses native diagonal/transvection
generation of the general linear group. -/
theorem lift_invertible_matrix (f : C →+* K) (hf : Function.Surjective f)
    (hunit : ∀ x : K, x ≠ 0 → ∃ u : Cˣ, f u = x)
    (U : Matrix ι ι K) (hU : IsUnit U) :
    ∃ V : Matrix ι ι C, IsUnit V ∧ V.map f = U := by
  classical
  apply Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun U => ∃ V : Matrix ι ι C, IsUnit V ∧ V.map f = U) U
    ((Matrix.isUnit_iff_isUnit_det U).mp hU).ne_zero
  · intro d hd
    have hd' : ∀ i, d i ≠ 0 := by simpa [det_diagonal, Finset.prod_ne_zero_iff] using hd
    choose u hu using fun i => hunit (d i) (hd' i)
    refine ⟨diagonal (fun i => (u i : C)), ?_, ?_⟩
    · apply IsUnit.of_mul_eq_one (diagonal (fun i => (↑((u i)⁻¹) : C)))
      simp [diagonal_mul_diagonal]
    · ext i j
      by_cases h : i = j <;> simp [Matrix.diagonal, h, hu]
  · intro t
    obtain ⟨c, hc⟩ := hf t.c
    let t' : TransvectionStruct ι C := ⟨t.i, t.j, t.hij, c⟩
    refine ⟨t'.toMatrix, IsUnit.of_mul_eq_one t'.inv.toMatrix t'.mul_inv, ?_⟩
    change f.mapMatrix (1 + Matrix.single t.i t.j c) =
      1 + Matrix.single t.i t.j t.c
    rw [map_add, map_one]
    congr 1
    ext i j
    change f (if t.i = i ∧ t.j = j then c else 0) =
      if t.i = i ∧ t.j = j then t.c else 0
    split_ifs <;> simp only [hc, map_zero]
  · intro U V _ _ hU hV
    obtain ⟨U', hU', rfl⟩ := hU
    obtain ⟨V', hV', rfl⟩ := hV
    exact ⟨U' * V', hU'.mul hV', map_mul f.mapMatrix U' V'⟩

end MatrixLift

section ScalarLift

variable {A K : Type*} [CommRing A] [Field K]

/-- A monic numerator and denominator define a genuine unit. -/
theorem isUnit_monic_fraction (p : A[X]) (hp : p.Monic) (q : monicSubmonoid A) :
    IsUnit (Localization.mk p q : MonicFrac A) := by
  refine IsUnit.of_mul_eq_one (Localization.mk q.val (⟨p, hp⟩ : monicSubmonoid A)) ?_
  simp only [Localization.mk_eq_mk'_apply]
  exact IsLocalization.mk'_mul_mk'_eq_one' p q hp

/-- Scalar units in the rational residue field lift through monic
localization whenever coefficient units lift. -/
theorem lift_monicFrac_unit (f : A →+* K) (hf : Function.Surjective f)
    (hunit : ∀ x : K, x ≠ 0 → ∃ u : Aˣ, f u = x)
    (a : MonicFrac K) (ha : a ≠ 0) :
    ∃ u : (MonicFrac A)ˣ, mapCoefficients f u = a := by
  revert ha
  refine Localization.induction_on a ?_
  rintro ⟨p, q⟩ ha
  have hp0 : p ≠ 0 := by
    intro hp
    apply ha
    subst p
    rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_zero]
  have hc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
  obtain ⟨r, hr⟩ := hunit p.leadingCoeff hc
  obtain ⟨p', hp', _, hpm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective hf (p * C p.leadingCoeff⁻¹))
    (monic_mul_leadingCoeff_inv hp0)
  obtain ⟨q', hq', _, hqm⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective hf q.val) q.property
  let qlift : monicSubmonoid A := ⟨q', hqm⟩
  let z : MonicFrac A := polynomialInclusion (C (r : A)) * Localization.mk p' qlift
  have hz : IsUnit z :=
    (r.isUnit.map ((algebraMap A[X] (MonicFrac A)).comp C)).mul
      (isUnit_monic_fraction p' hpm qlift)
  refine ⟨hz.unit, ?_⟩
  rw [hz.unit_spec]
  change mapCoefficients f (polynomialInclusion (C (r : A)) * Localization.mk p' qlift) = _
  rw [map_mul, mapCoefficients_polynomialInclusion, Polynomial.map_C, hr,
    mapCoefficients_mk, hp']
  have hd : (⟨qlift.val.map f, qlift.property.map f⟩ : monicSubmonoid K) = q :=
    Subtype.ext hq'
  rw [hd, polynomialInclusion_apply, ← Localization.mk_one_eq_algebraMap, Localization.mk_mul]
  simp only [one_mul]
  congr 1
  rw [mul_left_comm, ← C_mul, mul_inv_cancel₀ hc, C_1, mul_one]

end ScalarLift

section Residue

variable (A : Type*) [CommRing A] [IsLocalRing A]

/-- Native reduction of monic fractions to the rational residue field. -/
abbrev residueMap : MonicFrac A →+* MonicFrac (IsLocalRing.ResidueField A) :=
  mapCoefficients (IsLocalRing.residue A)

theorem residue_unit_lifts (a : MonicFrac (IsLocalRing.ResidueField A)) (ha : a ≠ 0) :
    ∃ u : (MonicFrac A)ˣ, residueMap A u = a := by
  apply lift_monicFrac_unit (IsLocalRing.residue A) IsLocalRing.residue_surjective
    (fun x hx => ?_) a ha
  obtain ⟨r, hr⟩ := IsLocalRing.residue_surjective (R := A) x
  have hu : IsUnit r := (IsLocalRing.residue_ne_zero_iff_isUnit r).mp (hr ▸ hx)
  exact ⟨hu.unit, by simpa only [hu.unit_spec] using hr⟩

/-- Every invertible matrix over the rational residue field lifts to an
invertible matrix over the actual monic localization. -/
theorem residue_GL_lifts {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι (MonicFrac (IsLocalRing.ResidueField A))) (hU : IsUnit U) :
    ∃ V : Matrix ι ι (MonicFrac A), IsUnit V ∧ V.map (residueMap A) = U :=
  lift_invertible_matrix (residueMap A)
    (mapCoefficients_surjective (IsLocalRing.residue A) IsLocalRing.residue_surjective)
    (residue_unit_lifts A) U hU

end Residue

end

end Decoupling.MonicResidue
