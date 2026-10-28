import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.Module.LocalizedModule.Away
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.RingTheory.Ideal.Span
import Mathlib.LinearAlgebra.Prod
import Mathlib.RingTheory.Flat.Localization
import Mathlib.RingTheory.Flat.EquationalCriterion
import Mathlib.RingTheory.LocalProperties.FinitePresentation

/-!
# The complementary cover in Swan's Laurent argument

Swan, *Projective modules over Laurent polynomial rings*, TAMS 237 (1978),
111–120, p.113, Lemma 1.3 uses the cover D(Y) ∪ D(f.reverse), where
Y = X⁻¹ and f is monic. This file proves the cover identity and genuine module
section gluing on any such two-element principal cover, with explicit
localization maps. It does not assert the still separate projective-module
extension theorem or the two-half freeness criterion from p.111.
-/

namespace Decoupling.LaurentFreeness

noncomputable section

set_option backward.isDefEq.respectTransparency false

section PolynomialCover

open Polynomial LaurentPolynomial

variable {A : Type*} [CommRing A]

/-- The opposite-half polynomial has constant term one, including degree zero. -/
theorem reverse_monic_constant {f : A[X]} (hf : f.Monic) : f.reverse.coeff 0 = 1 := by
  rw [coeff_zero_reverse, hf.leadingCoeff]

/-- Explicit Bezout identity for Swan's two affine charts. -/
theorem reverse_monic_bezout {f : A[X]} (hf : f.Monic) :
    (-f.reverse.divX) * X + f.reverse = 1 := by
  have h := divX_mul_X_add f.reverse
  rw [reverse_monic_constant hf, C_1] at h
  calc
    _ = (-f.reverse.divX) * X + (f.reverse.divX * X + 1) :=
      congrArg (fun p => (-f.reverse.divX) * X + p) h.symm
    _ = 1 := by ring

theorem reverse_monic_coprime {f : A[X]} (hf : f.Monic) : IsCoprime X f.reverse :=
  ⟨-f.reverse.divX, 1, by simpa using reverse_monic_bezout hf⟩

/-- Thus D(Y) and D(f.reverse) cover the whole opposite polynomial chart. -/
theorem reverse_monic_span {f : A[X]} (hf : f.Monic) :
    Ideal.span ({X, f.reverse} : Set A[X]) = ⊤ := by
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← reverse_monic_bezout hf]
  exact Ideal.add_mem _
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.subset_span (by simp))

theorem invert_involutive (p : LaurentPolynomial A) : invert (invert p) = p := by
  ext i
  simp

/-- The two denominators differ by a Laurent monomial unit on the overlap. -/
theorem opposite_denominator (f : A[X]) :
    invert (toLaurent f.reverse) = toLaurent f * T (-(f.natDegree : ℤ)) := by
  rw [toLaurent_reverse, map_mul, invert_involutive, invert_T]

theorem opposite_denominator_isUnit (f : A[X]) :
    IsUnit (invert (toLaurent f.reverse)) ↔ IsUnit (toLaurent f) := by
  rw [opposite_denominator, IsUnit.mul_iff]
  exact and_iff_left (isUnit_of_invertible _)

end PolynomialCover

section TwoChartGluing

variable {A : Type*} [CommRing A]
  {M M₁ M₂ M₁₂ : Type*}
  [AddCommGroup M] [Module A M]
  [AddCommGroup M₁] [Module A M₁]
  [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₁₂] [Module A M₁₂]
  {a b : A}
  (f : M →ₗ[A] M₁) (g : M →ₗ[A] M₂) (h : M →ₗ[A] M₁₂)
  [IsLocalizedModule.Away a f] [IsLocalizedModule.Away b g]
  [IsLocalizedModule.Away (a * b) h]
  (F : M₁ →ₗ[A] M₁₂) (G : M₂ →ₗ[A] M₁₂)
  (hF : F.comp f = h) (hG : G.comp g = h)

private theorem away_smul_injective {B N : Type*} [CommRing B]
    [AddCommGroup N] [Module B N] {V : Type*} [AddCommGroup V] [Module B V]
    (f : V →ₗ[B] N) (a : B) [IsLocalizedModule.Away a f] (i : ℕ) :
    Function.Injective (fun x : N => a ^ i • x) := by
  have hu := (IsLocalizedModule.Away.isUnit_algebraMap f a).pow i
  rw [← map_pow] at hu
  exact (Module.End.isUnit_iff _).mp hu |>.1

/-- Equality of sections is detected on a comaximal two-element cover. -/
theorem jointly_injective (hab : IsCoprime a b) : Function.Injective (f.prod g) := by
  intro x y hxy
  obtain ⟨i, hi⟩ := IsLocalizedModule.Away.exists_of_eq a (congrArg Prod.fst hxy)
  obtain ⟨j, hj⟩ := IsLocalizedModule.Away.exists_of_eq b (congrArg Prod.snd hxy)
  obtain ⟨s, t, hst⟩ := hab.pow (m := i) (n := j)
  calc
    x = (s * a ^ i + t * b ^ j) • x := by rw [hst, one_smul]
    _ = (s * a ^ i + t * b ^ j) • y := by simp only [add_smul, mul_smul, hi, hj]
    _ = y := by rw [hst, one_smul]

include hF hG in
/-- Compatible localized sections have an actual unique global section.
The proof clears the overlap denominator and uses a Bezout identity for powers. -/
theorem existsUnique_glue (hab : IsCoprime a b) (x : M₁) (y : M₂)
    (hxy : F x = G y) : ∃! m : M, f m = x ∧ g m = y := by
  obtain ⟨i, u, hu⟩ := IsLocalizedModule.Away.surj f a x
  obtain ⟨j, v, hv⟩ := IsLocalizedModule.Away.surj g b y
  have hFu (m : M) : F (f m) = h m := DFunLike.congr_fun hF m
  have hGv (m : M) : G (g m) = h m := DFunLike.congr_fun hG m
  have huv : h (b ^ j • u) = h (a ^ i • v) := by
    rw [← hFu, map_smul, map_smul, ← hu, map_smul, hxy,
      smul_comm (b ^ j) (a ^ i), ← map_smul, hv,
      hGv, map_smul]
  obtain ⟨k, hk⟩ := IsLocalizedModule.Away.exists_of_eq (a * b) huv
  let U := a ^ k • u
  let V := b ^ k • v
  have hUV : b ^ (j + k) • U = a ^ (i + k) • V := by
    simpa only [U, V, pow_add, mul_pow, smul_smul,
      mul_comm, mul_left_comm, mul_assoc] using hk
  have hU : f U = a ^ (i + k) • x := by
    simp only [U, map_smul, ← hu, smul_smul, pow_add, mul_comm]
  have hV : g V = b ^ (j + k) • y := by
    simp only [V, map_smul, ← hv, smul_smul, pow_add, mul_comm]
  obtain ⟨s, t, hst⟩ := hab.pow (m := i + k) (n := j + k)
  let m := s • U + t • V
  have hm₁ : a ^ (i + k) • m = U := by
    calc
      _ = s • (a ^ (i + k) • U) + t • (b ^ (j + k) • U) := by
        simp only [m, smul_add, smul_comm (a ^ (i + k)) s,
          smul_comm (a ^ (i + k)) t, hUV]
      _ = (s * a ^ (i + k) + t * b ^ (j + k)) • U := by
        rw [add_smul, mul_smul, mul_smul]
      _ = U := by rw [hst, one_smul]
  have hm₂ : b ^ (j + k) • m = V := by
    calc
      _ = s • (a ^ (i + k) • V) + t • (b ^ (j + k) • V) := by
        simp only [m, smul_add, smul_comm (b ^ (j + k)) s,
          smul_comm (b ^ (j + k)) t, hUV]
      _ = (s * a ^ (i + k) + t * b ^ (j + k)) • V := by
        rw [add_smul, mul_smul, mul_smul]
      _ = V := by rw [hst, one_smul]
  have hfm : f m = x := away_smul_injective f a (i + k) (by
    change a ^ (i + k) • f m = a ^ (i + k) • x
    rw [← map_smul, hm₁, hU])
  have hgm : g m = y := away_smul_injective g b (j + k) (by
    change b ^ (j + k) • g m = b ^ (j + k) • y
    rw [← map_smul, hm₂, hV])
  refine ⟨m, ⟨hfm, hgm⟩, ?_⟩
  intro z hz
  exact jointly_injective f g hab (Prod.ext (hz.1.trans hfm.symm) (hz.2.trans hgm.symm))

/-- The module of compatible sections on the two principal charts. -/
def compatibleSections : Submodule A (M₁ × M₂) :=
  LinearMap.ker (F.comp (LinearMap.fst A M₁ M₂) - G.comp (LinearMap.snd A M₁ M₂))

def toCompatibleSections : M →ₗ[A] compatibleSections F G :=
  (f.prod g).codRestrict _ (fun m => by
    change F (f m) - G (g m) = 0
    rw [show F (f m) = h m from DFunLike.congr_fun hF m,
      show G (g m) = h m from DFunLike.congr_fun hG m, sub_self])

/-- Effective two-chart descent, as a linear equivalence rather than a set-level assertion. -/
def gluingEquiv (hab : IsCoprime a b) : M ≃ₗ[A] compatibleSections F G :=
  LinearEquiv.ofBijective (toCompatibleSections f g h F G hF hG) ⟨by
    intro x y hxy
    exact jointly_injective f g hab (congrArg Subtype.val hxy), by
    intro z
    have hz : F z.1.1 = G z.1.2 := sub_eq_zero.mp z.property
    obtain ⟨m, hm, _⟩ := existsUnique_glue f g h F G hF hG hab z.1.1 z.1.2 hz
    exact ⟨m, Subtype.ext (Prod.ext hm.1 hm.2)⟩⟩

@[simp] theorem gluingEquiv_apply (hab : IsCoprime a b) (m : M) :
    (gluingEquiv f g h F G hF hG hab m).val = (f m, g m) := rfl

end TwoChartGluing

section ConstructedModule

variable {A : Type*} [CommRing A]
  {M₁ M₂ M₁₂ : Type*}
  [AddCommGroup M₁] [Module A M₁]
  [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₁₂] [Module A M₁₂]
  (F : M₁ →ₗ[A] M₁₂) (G : M₂ →ₗ[A] M₁₂)

def firstProjection : compatibleSections F G →ₗ[A] M₁ :=
  (LinearMap.fst A M₁ M₂).comp (compatibleSections F G).subtype

def secondProjection : compatibleSections F G →ₗ[A] M₂ :=
  (LinearMap.snd A M₁ M₂).comp (compatibleSections F G).subtype

/-- The constructed pullback module localizes to the first chart. No global
module is assumed to exist beforehand. -/
theorem firstProjection_isLocalized (a : A)
    (ha : IsUnit (algebraMap A (Module.End A M₁) a))
    [IsLocalizedModule.Away a G] : IsLocalizedModule.Away a (firstProjection F G) := by
  apply IsLocalizedModule.Away.mk ha
  · intro x
    obtain ⟨n, y, hy⟩ := IsLocalizedModule.Away.surj G a (F x)
    refine ⟨n, ⟨(a ^ n • x, y), ?_⟩, rfl⟩
    change F (a ^ n • x) - G y = 0
    rw [map_smul, hy, sub_self]
  · intro x y hxy
    have hx : F x.1.1 = G x.1.2 := sub_eq_zero.mp x.property
    have hy : F y.1.1 = G y.1.2 := sub_eq_zero.mp y.property
    have hGxy : G x.1.2 = G y.1.2 := hx.symm.trans ((congrArg F hxy).trans hy)
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq a hGxy
    exact ⟨n, Subtype.ext (Prod.ext (congrArg (fun z => a ^ n • z) hxy) hn)⟩

/-- The same constructed module localizes to the second chart. -/
theorem secondProjection_isLocalized (b : A)
    (hb : IsUnit (algebraMap A (Module.End A M₂) b))
    [IsLocalizedModule.Away b F] : IsLocalizedModule.Away b (secondProjection F G) := by
  apply IsLocalizedModule.Away.mk hb
  · intro y
    obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj F b (G y)
    refine ⟨n, ⟨(x, b ^ n • y), ?_⟩, rfl⟩
    change F x - G (b ^ n • y) = 0
    rw [map_smul, hx, sub_self]
  · intro x y hxy
    have hx : F x.1.1 = G x.1.2 := sub_eq_zero.mp x.property
    have hy : F y.1.1 = G y.1.2 := sub_eq_zero.mp y.property
    have hFxy : F x.1.1 = F y.1.1 := hx.trans ((congrArg G hxy).trans hy.symm)
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq b hFxy
    exact ⟨n, Subtype.ext (Prod.ext hn (congrArg (fun z => b ^ n • z) hxy))⟩

/-- Explicit first restriction equivalence of the module glued from two charts. -/
def firstChartEquiv (a : A)
    (ha : IsUnit (algebraMap A (Module.End A M₁) a)) [IsLocalizedModule.Away a G] :
    LocalizedModule.Away a (compatibleSections F G) ≃ₗ[A] M₁ := by
  letI := firstProjection_isLocalized F G a ha
  exact IsLocalizedModule.iso (Submonoid.powers a) (firstProjection F G)

def secondChartEquiv (b : A)
    (hb : IsUnit (algebraMap A (Module.End A M₂) b)) [IsLocalizedModule.Away b F] :
    LocalizedModule.Away b (compatibleSections F G) ≃ₗ[A] M₂ := by
  letI := secondProjection_isLocalized F G b hb
  exact IsLocalizedModule.iso (Submonoid.powers b) (secondProjection F G)

@[simp] theorem firstChartEquiv_mk (a : A)
    (ha : IsUnit (algebraMap A (Module.End A M₁) a)) [IsLocalizedModule.Away a G]
    (p : compatibleSections F G) :
    firstChartEquiv F G a ha (LocalizedModule.mk p 1) = p.1.1 := by
  let := firstProjection_isLocalized F G a ha
  exact IsLocalizedModule.iso_mk_one _ _ p

@[simp] theorem secondChartEquiv_mk (b : A)
    (hb : IsUnit (algebraMap A (Module.End A M₂) b)) [IsLocalizedModule.Away b F]
    (p : compatibleSections F G) :
    secondChartEquiv F G b hb (LocalizedModule.mk p 1) = p.1.2 := by
  let := secondProjection_isLocalized F G b hb
  exact IsLocalizedModule.iso_mk_one _ _ p

end ConstructedModule

section FiniteProjectiveGluing

variable {A : Type*} [CommRing A]
  {M₁ M₂ M₁₂ : Type*}
  [AddCommGroup M₁] [Module A M₁]
  [AddCommGroup M₂] [Module A M₂]
  [AddCommGroup M₁₂] [Module A M₁₂]
  (F : M₁ →ₗ[A] M₁₂) (G : M₂ →ₗ[A] M₁₂)
  (a b : A)
  [Module (Localization.Away a) M₁] [IsScalarTower A (Localization.Away a) M₁]
  [Module (Localization.Away b) M₂] [IsScalarTower A (Localization.Away b) M₂]
  [IsLocalizedModule.Away a G] [IsLocalizedModule.Away b F]

private theorem localized_scalar_isUnit (c : A) (N : Type*) [AddCommGroup N]
    [Module A N] [Module (Localization.Away c) N]
    [IsScalarTower A (Localization.Away c) N] :
    IsUnit (algebraMap A (Module.End A N) c) := by
  let := isLocalizedModule_id (Submonoid.powers c) N (Localization.Away c)
  exact IsLocalizedModule.Away.isUnit_algebraMap (LinearMap.id : N →ₗ[A] N) c

def firstChartLocalizedEquiv :
    LocalizedModule.Away a (compatibleSections F G) ≃ₗ[Localization.Away a] M₁ :=
  (firstChartEquiv F G a (localized_scalar_isUnit a M₁)).extendScalarsOfIsLocalization
    (Submonoid.powers a) (Localization.Away a)

def secondChartLocalizedEquiv :
    LocalizedModule.Away b (compatibleSections F G) ≃ₗ[Localization.Away b] M₂ :=
  (secondChartEquiv F G b (localized_scalar_isUnit b M₂)).extendScalarsOfIsLocalization
    (Submonoid.powers b) (Localization.Away b)

private theorem coprime_span (hab : IsCoprime a b) : Ideal.span ({a, b} : Set A) = ⊤ := by
  obtain ⟨s, t, hst⟩ := hab
  apply (Ideal.eq_top_iff_one _).mpr
  rw [← hst]
  exact Ideal.add_mem _
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

/-- Finite presentation descends for the explicitly constructed glued module. -/
theorem glued_finitePresentation (hab : IsCoprime a b)
    [Module.FinitePresentation (Localization.Away a) M₁]
    [Module.FinitePresentation (Localization.Away b) M₂] :
    Module.FinitePresentation A (compatibleSections F G) := by
  have ha : Module.FinitePresentation (Localization.Away a)
      (LocalizedModule.Away a (compatibleSections F G)) :=
    Module.FinitePresentation.of_equiv (R := Localization.Away a)
      (M := M₁) (N := LocalizedModule.Away a (compatibleSections F G))
      (firstChartLocalizedEquiv F G a).symm
  have hb : Module.FinitePresentation (Localization.Away b)
      (LocalizedModule.Away b (compatibleSections F G)) :=
    Module.FinitePresentation.of_equiv (R := Localization.Away b)
      (M := M₂) (N := LocalizedModule.Away b (compatibleSections F G))
      (secondChartLocalizedEquiv F G b).symm
  apply Module.FinitePresentation.of_localizationSpan ({a, b} : Set A) (coprime_span a b hab)
  intro c
  rcases c.property with hc | hc
  · rw [Set.mem_singleton_iff.mp hc]
    exact ha
  · rw [Set.mem_singleton_iff.mp hc]
    exact hb

/-- Flatness also descends through the same actual chart restrictions. -/
theorem glued_flat (hab : IsCoprime a b)
    [Module.Flat (Localization.Away a) M₁] [Module.Flat (Localization.Away b) M₂] :
    Module.Flat A (compatibleSections F G) := by
  have ha' : Module.Flat (Localization.Away a)
      (LocalizedModule.Away a (compatibleSections F G)) :=
    Module.Flat.of_linearEquiv (firstChartLocalizedEquiv F G a)
  have hb' : Module.Flat (Localization.Away b)
      (LocalizedModule.Away b (compatibleSections F G)) :=
    Module.Flat.of_linearEquiv (secondChartLocalizedEquiv F G b)
  have ha : Module.Flat A (LocalizedModule.Away a (compatibleSections F G)) :=
    (Module.flat_iff_of_isLocalization (Localization.Away a) (Submonoid.powers a) _).mp ha'
  have hb : Module.Flat A (LocalizedModule.Away b (compatibleSections F G)) :=
    (Module.flat_iff_of_isLocalization (Localization.Away b) (Submonoid.powers b) _).mp hb'
  apply Module.flat_of_localized_span A (compatibleSections F G) ({a, b} : Set A)
    (coprime_span a b hab)
  intro c
  rcases c.property with hc | hc
  · rw [Set.mem_singleton_iff.mp hc]
    exact ha
  · rw [Set.mem_singleton_iff.mp hc]
    exact hb

/-- Two finite projective chart modules glue to a finite projective module.
This proves the algebraic gluing operation used in Swan's extension argument;
it does not assume an extension or a global free basis. -/
theorem glued_finite_projective (hab : IsCoprime a b)
    [Module.Finite (Localization.Away a) M₁] [Module.Projective (Localization.Away a) M₁]
    [Module.Finite (Localization.Away b) M₂] [Module.Projective (Localization.Away b) M₂] :
    Module.Finite A (compatibleSections F G) ∧ Module.Projective A (compatibleSections F G) := by
  have := Module.finitePresentation_of_projective (Localization.Away a) M₁
  have := Module.finitePresentation_of_projective (Localization.Away b) M₂
  have := glued_finitePresentation F G a b hab
  have := glued_flat F G a b hab
  exact ⟨inferInstance, Module.Flat.projective_of_finitePresentation⟩

end FiniteProjectiveGluing

end
end Decoupling.LaurentFreeness
