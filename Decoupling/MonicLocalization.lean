import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Lifts
import Mathlib.RingTheory.Localization.Basic

/-!
# Polynomial parts in the localization at monic polynomials

This develops the actual localization appearing in Dicks, arXiv:2112.02272v1,
Lemma 3(i): https://arxiv.org/html/2112.02272v1 . Unlike the later Horrocks
theorem, the polynomial-part decomposition itself does not require a local
coefficient ring. We retain the nontriviality required for strict degree
inequalities and use native polynomial division and native localization.
-/

namespace Decoupling.MonicLocalization

open Polynomial

noncomputable section

variable (A : Type*) [CommRing A]

/-- All monic polynomials, as the actual multiplicative denominator set. -/
def monicSubmonoid : Submonoid A[X] where
  carrier := {f | f.Monic}
  one_mem' := monic_one
  mul_mem' := fun hf hg => hf.mul hg

/-- Dicks' `A(x)`, localized at all monic polynomials. -/
abbrev MonicFrac := Localization (monicSubmonoid A)

variable {A} [Nontrivial A]

/-- Multiplying numerator and denominator by a monic polynomial preserves
the polynomial quotient. This is the representative-independence step. -/
theorem divByMonic_mul_right (f g h : A[X]) (hg : g.Monic) (hh : h.Monic) :
    (f * h) /ₘ (g * h) = f /ₘ g := by
  apply (div_modByMonic_unique (f /ₘ g) ((f %ₘ g) * h) (hg.mul hh) _).1
  constructor
  · calc
      f %ₘ g * h + g * h * (f /ₘ g) = (f %ₘ g + g * (f /ₘ g)) * h := by ring
      _ = f * h := by rw [modByMonic_add_div]
  · rw [hh.degree_mul, hh.degree_mul, degree_eq_natDegree hh.ne_zero]
    exact WithBot.add_lt_add_right (by simp) (degree_modByMonic_lt f hg)

private theorem quotient_wellDefined {f f' : A[X]} {g g' : monicSubmonoid A}
    (h : Localization.r (monicSubmonoid A) (f, g) (f', g')) :
    f /ₘ (g : A[X]) = f' /ₘ (g' : A[X]) := by
  obtain ⟨s, hs⟩ := Localization.r_iff_exists.mp h
  have heq : (g' : A[X]) * f = (g : A[X]) * f' := s.property.isRegular.left hs
  calc
    f /ₘ (g : A[X]) = (f * (g' : A[X])) /ₘ ((g : A[X]) * (g' : A[X])) :=
      (divByMonic_mul_right f g g' g.property g'.property).symm
    _ = (f' * (g : A[X])) /ₘ ((g' : A[X]) * (g : A[X])) := by
      rw [mul_comm f _, heq, mul_comm g.val f', mul_comm g.val g'.val]
    _ = f' /ₘ (g' : A[X]) := divByMonic_mul_right f' g' g g'.property g.property

/-- The polynomial part of a monic fraction. -/
def polynomialPartFun (a : MonicFrac A) : A[X] :=
  Localization.liftOn a (fun f g => f /ₘ (g : A[X])) (fun h => quotient_wellDefined h)

@[simp] theorem polynomialPartFun_mk (f : A[X]) (g : monicSubmonoid A) :
    polynomialPartFun (Localization.mk f g) = f /ₘ (g : A[X]) := rfl

/-- Polynomial-part extraction is linear over the coefficient ring. -/
def polynomialPart : MonicFrac A →ₗ[A] A[X] where
  toFun := polynomialPartFun
  map_add' a b := by
    refine Localization.induction_on₂ a b ?_
    rintro ⟨f, g⟩ ⟨f', g'⟩
    rw [Localization.add_mk, polynomialPartFun_mk, polynomialPartFun_mk,
      polynomialPartFun_mk]
    change ((g : A[X]) * f' + (g' : A[X]) * f) /ₘ ((g : A[X]) * (g' : A[X])) = _
    rw [add_divByMonic]
    have h₁ : ((g : A[X]) * f') /ₘ ((g : A[X]) * (g' : A[X])) = f' /ₘ (g' : A[X]) := by
      rw [mul_comm g.val f', mul_comm g.val g'.val]
      exact divByMonic_mul_right f' g' g g'.property g.property
    have h₂ : ((g' : A[X]) * f) /ₘ ((g : A[X]) * (g' : A[X])) = f /ₘ (g : A[X]) := by
      rw [mul_comm g'.val f]
      exact divByMonic_mul_right f g g' g.property g'.property
    rw [h₁, h₂, add_comm]
  map_smul' c a := by
    refine Localization.induction_on a ?_
    rintro ⟨f, g⟩
    rw [Localization.smul_mk, polynomialPartFun_mk, polynomialPartFun_mk]
    exact smul_divByMonic c f

@[simp] theorem polynomialPart_mk (f : A[X]) (g : monicSubmonoid A) :
    polynomialPart (Localization.mk f g) = f /ₘ (g : A[X]) := rfl

/-- The native algebra inclusion of polynomials, viewed over the coefficients. -/
def polynomialInclusion : A[X] →ₗ[A] MonicFrac A :=
  (IsScalarTower.toAlgHom A A[X] (MonicFrac A)).toLinearMap

omit [Nontrivial A] in
theorem polynomialInclusion_apply (f : A[X]) :
    polynomialInclusion f = algebraMap A[X] (MonicFrac A) f := rfl

@[simp] theorem polynomialPart_polynomialInclusion (f : A[X]) :
    polynomialPart (polynomialInclusion f) = f := by
  rw [polynomialInclusion_apply, ← Localization.mk_one_eq_algebraMap, polynomialPart_mk]
  simp

@[simp] theorem polynomialPart_algebraMap (f : A[X]) :
    polynomialPart (algebraMap A[X] (MonicFrac A) f) = f :=
  polynomialPart_polynomialInclusion f

@[simp] theorem polynomialPart_one : polynomialPart (1 : MonicFrac A) = 1 := by
  rw [← map_one (algebraMap A[X] (MonicFrac A)), polynomialPart_algebraMap]

theorem polynomialInclusion_injective : Function.Injective (polynomialInclusion (A := A)) :=
  Function.LeftInverse.injective polynomialPart_polynomialInclusion

/-- The proper fractions form the kernel of the actual polynomial-part map. -/
def properFractions : Submodule A (MonicFrac A) := LinearMap.ker polynomialPart

@[simp] theorem mk_mem_properFractions_iff (f : A[X]) (g : monicSubmonoid A) :
    Localization.mk f g ∈ properFractions (A := A) ↔ f.degree < (g : A[X]).degree :=
  divByMonic_eq_zero_iff g.property

/-- Each fraction has a unique polynomial part and a proper-fraction part. -/
def polynomialProperDecomposition : MonicFrac A ≃ₗ[A] A[X] × properFractions (A := A) where
  toFun a := (polynomialPart a, ⟨a - polynomialInclusion (polynomialPart a), by
    change polynomialPart (a - polynomialInclusion (polynomialPart a)) = 0
    simp⟩)
  invFun a := polynomialInclusion a.1 + a.2.val
  left_inv a := by simp
  right_inv a := by
    rcases a with ⟨p, r, hr⟩
    have hz : polynomialPart r = 0 := hr
    apply Prod.ext
    · simp [hz]
    · apply Subtype.ext
      simp [hz]
  map_add' a b := by
    apply Prod.ext
    · exact map_add polynomialPart a b
    · apply Subtype.ext
      change a + b - polynomialInclusion (polynomialPart (a + b)) =
        (a - polynomialInclusion (polynomialPart a)) +
          (b - polynomialInclusion (polynomialPart b))
      rw [map_add, map_add]
      abel
  map_smul' c a := by
    apply Prod.ext
    · exact map_smul polynomialPart c a
    · apply Subtype.ext
      change c • a - polynomialInclusion (polynomialPart (c • a)) =
        c • (a - polynomialInclusion (polynomialPart a))
      simp [smul_sub]

/-- Proper fractions are closed under multiplication. -/
theorem properFractions_mul {a b : MonicFrac A}
    (ha : a ∈ properFractions (A := A)) (hb : b ∈ properFractions (A := A)) :
    a * b ∈ properFractions (A := A) := by
  revert ha hb
  refine Localization.induction_on₂ a b ?_
  rintro ⟨f, g⟩ ⟨f', g'⟩ hf hf'
  rw [mk_mem_properFractions_iff] at hf hf'
  rw [Localization.mk_mul, mk_mem_properFractions_iff]
  change (f * f').degree < ((g : A[X]) * (g' : A[X])).degree
  rw [g'.property.degree_mul]
  calc
    (f * f').degree ≤ f.degree + f'.degree := degree_mul_le f f'
    _ ≤ f.degree + (g' : A[X]).degree := add_le_add le_rfl hf'.le
    _ < (g : A[X]).degree + (g' : A[X]).degree :=
      WithBot.add_lt_add_right (degree_ne_bot.mpr g'.property.ne_zero) hf

omit [Nontrivial A] in
private theorem one_add_mk (f : A[X]) (g : monicSubmonoid A) :
    (1 : MonicFrac A) + Localization.mk f g = Localization.mk ((g : A[X]) + f) g := by
  rw [← Localization.mk_self g, Localization.add_mk_self]

/-- Adding a proper fraction to one always gives a unit: the new numerator
is monic of the same degree as the denominator. -/
theorem isUnit_one_add {a : MonicFrac A} (ha : a ∈ properFractions (A := A)) :
    IsUnit (1 + a) := by
  revert ha
  refine Localization.induction_on a ?_
  rintro ⟨f, g⟩ hf
  rw [mk_mem_properFractions_iff] at hf
  rw [one_add_mk]
  let h : monicSubmonoid A := ⟨(g : A[X]) + f, g.property.add_of_left hf⟩
  apply isUnit_iff_exists_inv.mpr
  refine ⟨Localization.mk (g : A[X]) h, ?_⟩
  rw [Localization.mk_mul]
  change Localization.mk ((h : A[X]) * (g : A[X])) (g * h) = 1
  rw [mul_comm]
  exact Localization.mk_self (g * h)

/-- The inverse of `1 + a` again differs from one by a proper fraction. -/
theorem exists_proper_inverse {a : MonicFrac A} (ha : a ∈ properFractions (A := A)) :
    ∃ b ∈ properFractions (A := A), (1 + a) * (1 + b) = 1 := by
  revert ha
  refine Localization.induction_on a ?_
  rintro ⟨f, g⟩ hf
  rw [mk_mem_properFractions_iff] at hf
  let h : monicSubmonoid A := ⟨(g : A[X]) + f, g.property.add_of_left hf⟩
  refine ⟨Localization.mk (-f) h, ?_, ?_⟩
  · rw [mk_mem_properFractions_iff, degree_neg]
    change f.degree < ((g : A[X]) + f).degree
    rw [degree_add_eq_left_of_degree_lt hf]
    exact hf
  · rw [one_add_mk, one_add_mk, Localization.mk_mul]
    have hcancel : (h : A[X]) + -f = (g : A[X]) := by dsimp [h]; abel
    rw [hcancel]
    change Localization.mk ((h : A[X]) * (g : A[X])) (g * h) = 1
    rw [mul_comm]
    exact Localization.mk_self (g * h)

section Coefficients

variable {B : Type*} [CommRing B]

omit [Nontrivial A] in
/-- Coefficient homomorphisms extend to the actual monic localizations. -/
def mapCoefficients (f : A →+* B) : MonicFrac A →+* MonicFrac B :=
  IsLocalization.map (M := monicSubmonoid A) (S := MonicFrac A)
    (T := monicSubmonoid B) (MonicFrac B) (Polynomial.mapRingHom f)
    (fun _ h => Polynomial.Monic.map f h)

omit [Nontrivial A] in
@[simp] theorem mapCoefficients_mk (f : A →+* B) (p : A[X]) (q : monicSubmonoid A) :
    mapCoefficients f (Localization.mk p q) =
      Localization.mk (p.map f) (⟨q.val.map f, q.property.map f⟩ : monicSubmonoid B) := by
  simp only [mapCoefficients, Localization.mk_eq_mk'_apply]
  exact IsLocalization.map_mk' (M := monicSubmonoid A) (S := MonicFrac A)
    (T := monicSubmonoid B) (Q := MonicFrac B) (g := Polynomial.mapRingHom f)
    (fun _ h => Polynomial.Monic.map f h) p q

variable [Nontrivial B]

omit [Nontrivial A] in
/-- Surjective coefficient reduction gives a surjection on monic
localizations, because monic denominators lift to monic denominators. -/
theorem mapCoefficients_surjective (f : A →+* B) (hf : Function.Surjective f) :
    Function.Surjective (mapCoefficients f) := by
  intro a
  refine Localization.induction_on a ?_
  rintro ⟨p, q⟩
  obtain ⟨p', hp'⟩ := Polynomial.map_surjective f hf p
  obtain ⟨q', hq', _, hmonic⟩ := Polynomial.lifts_and_degree_eq_and_monic
    (Polynomial.mem_lifts_of_surjective hf q.val) q.property
  refine ⟨Localization.mk p' (⟨q', hmonic⟩ : monicSubmonoid A), ?_⟩
  rw [mapCoefficients_mk, hp']
  congr 1
  exact Subtype.ext hq'

omit [Nontrivial A] [Nontrivial B] in
@[simp] theorem mapCoefficients_polynomialInclusion (f : A →+* B) (p : A[X]) :
    mapCoefficients f (polynomialInclusion p) = polynomialInclusion (p.map f) := by
  rw [polynomialInclusion_apply, ← Localization.mk_one_eq_algebraMap,
    mapCoefficients_mk, polynomialInclusion_apply, ← Localization.mk_one_eq_algebraMap]
  congr 1
  apply Subtype.ext
  exact Polynomial.map_one f

/-- Polynomial-part extraction commutes with coefficient reduction,
including passage to the residue field in Horrocks' theorem. -/
theorem polynomialPart_mapCoefficients (f : A →+* B) (a : MonicFrac A) :
    polynomialPart (mapCoefficients f a) = (polynomialPart a).map f := by
  refine Localization.induction_on a ?_
  rintro ⟨p, q⟩
  rw [mapCoefficients_mk, polynomialPart_mk, polynomialPart_mk]
  exact (Polynomial.map_divByMonic f q.property).symm

theorem mapCoefficients_proper (f : A →+* B) {a : MonicFrac A}
    (ha : a ∈ properFractions (A := A)) :
    mapCoefficients f a ∈ properFractions (A := B) := by
  change polynomialPart (mapCoefficients f a) = 0
  rw [polynomialPart_mapCoefficients, show polynomialPart a = 0 from ha, Polynomial.map_zero]

end Coefficients

end

end Decoupling.MonicLocalization
