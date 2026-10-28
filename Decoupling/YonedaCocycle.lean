import Decoupling.ZeroComparison
import Decoupling.ExtCokernel

/-!
# The Yoneda cocycle and its coboundaries

This file treats the general degree-two comparison component in Appendix D.1
of `notes/main.pdf`.  The obstruction is mathlib's genuine derived-category
`Ext²`, represented using two consecutive syzygy short exact sequences.
The cokernel of restriction `Hom(P₁,E) → Hom(K₂,E)` is proved equivalent
to this Ext group when the two cover modules are projective.

Category composition is left-to-right.  Thus `a₂ ≫ h` is the paper's
`h a₂`.  Statements with subtraction work over arbitrary rings; subtraction
is addition for the manuscript's characteristic-two Laurent ring.
-/

universe w v u t

noncomputable section

namespace Decoupling.YonedaCocycle

open CategoryTheory CategoryTheory.Abelian

section Abstract

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {U : ShortComplex C} (hU : U.ShortExact)
  {K₂ P₁ : C} {a₂ : K₂ ⟶ P₁} {a₁ : P₁ ⟶ U.X₁} {zero : a₂ ≫ a₁ = 0}
  (hV : (ShortComplex.mk a₂ a₁ zero).ShortExact)
  {E : C}

/-- The genuine degree-two class represented by a map from the second syzygy. -/
def cocycleClass (f : K₂ ⟶ E) : Ext U.X₃ E 2 :=
  hU.extClass.comp (hV.extClass.comp (Ext.mk₀ f) (add_zero 1)) (by decide)

/-- The cocycle is zero exactly when it extends over the degree-one cover.
Only the degree-zero cover must be projective for this vanishing criterion. -/
theorem cocycleClass_zero_iff [Projective U.X₂] (f : K₂ ⟶ E) :
    cocycleClass hU hV f = 0 ↔ ∃ h : P₁ ⟶ E, a₂ ≫ h = f := by
  rw [cocycleClass, ExtSplitting.dimensionShift_zero_iff hU]
  constructor
  · intro hf
    obtain ⟨e, he⟩ := Ext.contravariant_sequence_exact₁ hV E (Ext.mk₀ f) (add_zero 1) hf
    obtain ⟨h, rfl⟩ := (Ext.mk₀_bijective P₁ E).surjective e
    refine ⟨h, (Ext.mk₀_bijective K₂ E).injective ?_⟩
    simpa only [Ext.mk₀_comp_mk₀] using he
  · rintro ⟨h, rfl⟩
    rw [← Ext.mk₀_comp_mk₀]
    exact hV.extClass_comp_assoc (Ext.mk₀ h)

theorem cocycleClass_sub (f g : K₂ ⟶ E) :
    cocycleClass hU hV (f - g) = cocycleClass hU hV f - cocycleClass hU hV g := by
  simp [cocycleClass, sub_eq_add_neg, Ext.mk₀_add]

/-- Equality of genuine classes is precisely equality modulo a coboundary. -/
theorem cocycleClass_eq_iff [Projective U.X₂] (f g : K₂ ⟶ E) :
    cocycleClass hU hV f = cocycleClass hU hV g ↔
      ∃ h : P₁ ⟶ E, a₂ ≫ h = f - g := by
  rw [← sub_eq_zero, ← cocycleClass_sub, cocycleClass_zero_iff]

/-- Naturality identifies the comparison cocycle with the actual Yoneda splice. -/
theorem cocycleClass_eq_splice {S : ShortComplex C} (hS : S.ShortExact)
    {Q : C} {j : S.X₃ ⟶ Q} {p : Q ⟶ U.X₃} {jp : j ≫ p = 0}
    (hT : (ShortComplex.mk j p jp).ShortExact)
    (f : K₂ ⟶ S.X₁) (q₁ : P₁ ⟶ S.X₂) (k : U.X₁ ⟶ S.X₃)
    (q₀ : U.X₂ ⟶ Q)
    (square₂ : f ≫ S.f = a₂ ≫ q₁)
    (square₁ : q₁ ≫ S.g = a₁ ≫ k)
    (square₀ : k ≫ j = U.f ≫ q₀)
    (endpoint : q₀ ≫ p = U.g) :
    cocycleClass hU hV f = hT.extClass.comp hS.extClass (by decide) := by
  let headComparison : ShortComplex.mk a₂ a₁ zero ⟶ S := {
    τ₁ := f
    τ₂ := q₁
    τ₃ := k
    comm₁₂ := square₂
    comm₂₃ := square₁
  }
  let tailComparison : U ⟶ ShortComplex.mk j p jp := {
    τ₁ := k
    τ₂ := q₀
    τ₃ := 𝟙 U.X₃
    comm₁₂ := square₀
    comm₂₃ := by simpa only [Category.comp_id] using endpoint
  }
  have hhead : hV.extClass.comp (Ext.mk₀ f) (add_zero 1) =
      (Ext.mk₀ k).comp hS.extClass (zero_add 1) :=
    hV.extClass_naturality hS headComparison
  have htail : hU.extClass.comp (Ext.mk₀ k) (add_zero 1) = hT.extClass := by
    simpa only [tailComparison, Ext.mk₀_id_comp] using
      hU.extClass_naturality hT tailComparison
  rw [cocycleClass, hhead, ← Ext.comp_assoc_of_second_deg_zero, htail]

include hU hV in
/-- The full cocycle/coboundary criterion for an arbitrary compared two-extension. -/
theorem splice_zero_iff_coboundary [Projective U.X₂]
    {S : ShortComplex C} (hS : S.ShortExact)
    {Q : C} {j : S.X₃ ⟶ Q} {p : Q ⟶ U.X₃} {jp : j ≫ p = 0}
    (hT : (ShortComplex.mk j p jp).ShortExact)
    (f : K₂ ⟶ S.X₁) (q₁ : P₁ ⟶ S.X₂) (k : U.X₁ ⟶ S.X₃)
    (q₀ : U.X₂ ⟶ Q)
    (square₂ : f ≫ S.f = a₂ ≫ q₁)
    (square₁ : q₁ ≫ S.g = a₁ ≫ k)
    (square₀ : k ≫ j = U.f ≫ q₀)
    (endpoint : q₀ ≫ p = U.g) :
    hT.extClass.comp hS.extClass (by decide : 1 + 1 = 2) = 0 ↔
      ∃ h : P₁ ⟶ S.X₁, a₂ ≫ h = f := by
  rw [← cocycleClass_eq_splice hU hV hS hT f q₁ k q₀
    square₂ square₁ square₀ endpoint, cocycleClass_zero_iff]

/-- A comparison from a resolution prefix into a two-extension.  The map `b`
is the surjection from `P₂` onto the second syzygy; its differential is `b ≫ a₂`. -/
structure Comparison {P₂ : C} (b : P₂ ⟶ K₂)
    (S : ShortComplex C) {Q : C} (j : S.X₃ ⟶ Q) (p : Q ⟶ U.X₃) where
  f₂ : P₂ ⟶ S.X₁
  q₁ : P₁ ⟶ S.X₂
  k : U.X₁ ⟶ S.X₃
  q₀ : U.X₂ ⟶ Q
  square₂ : f₂ ≫ S.f = (b ≫ a₂) ≫ q₁
  square₁ : q₁ ≫ S.g = a₁ ≫ k
  square₀ : k ≫ j = U.f ≫ q₀
  endpoint : q₀ ≫ p = U.g

namespace Comparison

variable {P₂ : C} {b : P₂ ⟶ K₂} {S : ShortComplex C} (hS : S.ShortExact)
  {Q : C} {j : S.X₃ ⟶ Q} {p : Q ⟶ U.X₃}
  (d : Comparison (a₂ := a₂) (a₁ := a₁) b S j p)

include zero in
omit [HasExt C] in
private theorem restrict_composite_zero : (a₂ ≫ d.q₁) ≫ S.g = 0 := by
  rw [Category.assoc, d.square₁, ← Category.assoc, zero]
  simp

/-- The degree-two comparison component factored through the second syzygy. -/
def syzygyComponent : K₂ ⟶ S.X₁ := by
  letI : Mono S.f := hS.mono_f
  exact hS.exact.lift (a₂ ≫ d.q₁) (d.restrict_composite_zero (zero := zero))

omit [HasExt C] in
theorem syzygyComponent_spec :
    d.syzygyComponent (zero := zero) hS ≫ S.f = a₂ ≫ d.q₁ := by
  let : Mono S.f := hS.mono_f
  exact hS.exact.lift_f _ _

omit [HasExt C] in
/-- The original comparison component is the pullback of its syzygy representative. -/
theorem component_eq : b ≫ d.syzygyComponent (zero := zero) hS = d.f₂ := by
  let : Mono S.f := hS.mono_f
  apply (cancel_mono S.f).mp
  rw [Category.assoc, syzygyComponent_spec, ← Category.assoc, d.square₂]

include hS in
omit [HasExt C] in
/-- Every comparison component satisfies the actual Hom-complex cocycle equation. -/
theorem component_cocycle {P₃ : C} (a₃ : P₃ ⟶ P₂)
    (h₃ : a₃ ≫ (b ≫ a₂) = 0) : a₃ ≫ d.f₂ = 0 := by
  let : Mono S.f := hS.mono_f
  apply (cancel_mono S.f).mp
  rw [Category.assoc, d.square₂, ← Category.assoc, h₃]
  simp

theorem class_eq_splice {jp : j ≫ p = 0}
    (hT : (ShortComplex.mk j p jp).ShortExact) :
    cocycleClass hU hV (d.syzygyComponent (zero := zero) hS) =
      hT.extClass.comp hS.extClass (by decide : 1 + 1 = 2) :=
  cocycleClass_eq_splice hU hV hS hT _ d.q₁ d.k d.q₀
    (d.syzygyComponent_spec (zero := zero) hS) d.square₁ d.square₀ d.endpoint

include hU hV in
/-- The full Appendix D.1 vanishing criterion for the actual `P₂` component. -/
theorem splice_zero_iff_component [Projective U.X₂] [Epi b] {jp : j ≫ p = 0}
    (hT : (ShortComplex.mk j p jp).ShortExact) :
    hT.extClass.comp hS.extClass (by decide : 1 + 1 = 2) = 0 ↔
      ∃ h : P₁ ⟶ S.X₁, (b ≫ a₂) ≫ h = d.f₂ := by
  rw [← d.class_eq_splice hU hV hS hT, cocycleClass_zero_iff]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h, by rw [Category.assoc, hh, d.component_eq (zero := zero) hS]⟩
  · rintro ⟨h, hh⟩
    refine ⟨h, (cancel_epi b).mp ?_⟩
    rw [← Category.assoc, hh, d.component_eq (zero := zero) hS]

include hU hV hS in
/-- Any two comparisons change the degree-two representative by a coboundary.
The formula becomes `f̂ + f = h a₂` in characteristic two. -/
theorem representative_independence [Projective U.X₂] {jp : j ≫ p = 0}
    (hT : (ShortComplex.mk j p jp).ShortExact)
    (d' : Comparison (a₂ := a₂) (a₁ := a₁) b S j p) :
    ∃ h : P₁ ⟶ S.X₁, (b ≫ a₂) ≫ h = d'.f₂ - d.f₂ := by
  have heq : cocycleClass hU hV (d'.syzygyComponent (zero := zero) hS) =
      cocycleClass hU hV (d.syzygyComponent (zero := zero) hS) := by
    rw [d'.class_eq_splice hU hV hS hT, d.class_eq_splice hU hV hS hT]
  obtain ⟨h, hh⟩ := (cocycleClass_eq_iff hU hV _ _).mp heq
  refine ⟨h, ?_⟩
  rw [Category.assoc, hh, Preadditive.comp_sub,
    d'.component_eq (zero := zero) hS, d.component_eq (zero := zero) hS]

end Comparison

/-- A morphism of two-extensions fixing both endpoints preserves the genuine
Yoneda class.  Consequently any finite zigzag of such morphisms preserves it. -/
theorem fixed_endpoint_invariance
    {S : ShortComplex C} (hS : S.ShortExact)
    {Q B : C} {j : S.X₃ ⟶ Q} {p : Q ⟶ B} {jp : j ≫ p = 0}
    (hT : (ShortComplex.mk j p jp).ShortExact)
    {N' L' Q' : C} {i' : S.X₁ ⟶ N'} {π' : N' ⟶ L'} {iπ' : i' ≫ π' = 0}
    (hS' : (ShortComplex.mk i' π' iπ').ShortExact)
    {j' : L' ⟶ Q'} {p' : Q' ⟶ B} {jp' : j' ≫ p' = 0}
    (hT' : (ShortComplex.mk j' p' jp').ShortExact)
    (α₁ : S.X₂ ⟶ N') (ℓ : S.X₃ ⟶ L') (α₀ : Q ⟶ Q')
    (left : i' = S.f ≫ α₁) (middle₁ : α₁ ≫ π' = S.g ≫ ℓ)
    (middle₀ : ℓ ≫ j' = j ≫ α₀) (right : α₀ ≫ p' = p) :
    hT.extClass.comp hS.extClass (by decide : 1 + 1 = 2) =
      hT'.extClass.comp hS'.extClass (by decide : 1 + 1 = 2) := by
  let headMap : S ⟶ ShortComplex.mk i' π' iπ' := {
    τ₁ := 𝟙 S.X₁
    τ₂ := α₁
    τ₃ := ℓ
    comm₁₂ := by simpa only [Category.id_comp] using left
    comm₂₃ := middle₁
  }
  let tailMap : ShortComplex.mk j p jp ⟶ ShortComplex.mk j' p' jp' := {
    τ₁ := ℓ
    τ₂ := α₀
    τ₃ := 𝟙 B
    comm₁₂ := middle₀
    comm₂₃ := by simpa only [Category.comp_id] using right
  }
  have hh : hS.extClass = (Ext.mk₀ ℓ).comp hS'.extClass (zero_add 1) := by
    simpa only [headMap, Ext.comp_mk₀_id] using hS.extClass_naturality hS' headMap
  have ht : hT.extClass.comp (Ext.mk₀ ℓ) (add_zero 1) = hT'.extClass := by
    simpa only [tailMap, Ext.mk₀_id_comp] using hT.extClass_naturality hT' tailMap
  rw [hh, ← Ext.comp_assoc_of_second_deg_zero, ht]

/-- Precomposing a representative by a resolution comparison preserves its
genuine Ext class.  Thus changing projective resolution cannot kill a nonzero class. -/
theorem change_resolution_preserves_class
    {K₁' P₀' : C} {i₀' : K₁' ⟶ P₀'} {ε' : P₀' ⟶ U.X₃} {zero₀' : i₀' ≫ ε' = 0}
    (hU' : (ShortComplex.mk i₀' ε' zero₀').ShortExact)
    {K₂' P₁' : C} {a₂' : K₂' ⟶ P₁'} {a₁' : P₁' ⟶ K₁'} {zero₁' : a₂' ≫ a₁' = 0}
    (hV' : (ShortComplex.mk a₂' a₁' zero₁').ShortExact)
    (χ₂ : K₂' ⟶ K₂) (χ₁ : P₁' ⟶ P₁) (χK₁ : K₁' ⟶ U.X₁) (χ₀ : P₀' ⟶ U.X₂)
    (square₂ : χ₂ ≫ a₂ = a₂' ≫ χ₁) (square₁ : χ₁ ≫ a₁ = a₁' ≫ χK₁)
    (square₀ : χK₁ ≫ U.f = i₀' ≫ χ₀) (endpoint : χ₀ ≫ U.g = ε') (f : K₂ ⟶ E) :
    cocycleClass hU' hV' (χ₂ ≫ f) = cocycleClass hU hV f := by
  let headMap : ShortComplex.mk a₂' a₁' zero₁' ⟶ ShortComplex.mk a₂ a₁ zero := {
    τ₁ := χ₂
    τ₂ := χ₁
    τ₃ := χK₁
    comm₁₂ := square₂
    comm₂₃ := square₁
  }
  let tailMap : ShortComplex.mk i₀' ε' zero₀' ⟶ U := {
    τ₁ := χK₁
    τ₂ := χ₀
    τ₃ := 𝟙 U.X₃
    comm₁₂ := square₀
    comm₂₃ := by simpa only [Category.comp_id] using endpoint
  }
  have hh := hV'.extClass_naturality hV headMap
  have ht : hU'.extClass.comp (Ext.mk₀ χK₁) (add_zero 1) = hU.extClass := by
    simpa only [tailMap, Ext.mk₀_id_comp] using hU'.extClass_naturality hU tailMap
  have hhf : hV'.extClass.comp (Ext.mk₀ (χ₂ ≫ f)) (add_zero 1) =
      (Ext.mk₀ χK₁).comp (hV.extClass.comp (Ext.mk₀ f) (add_zero 1)) (zero_add 1) := by
    rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_third_deg_zero]
    rw [show hV'.extClass.comp (Ext.mk₀ χ₂) (add_zero 1) =
      (Ext.mk₀ χK₁).comp hV.extClass (zero_add 1) from hh]
    exact Ext.comp_assoc_of_third_deg_zero _ _ _ _
  rw [cocycleClass, hhf, ← Ext.comp_assoc_of_second_deg_zero, ht]
  rfl

section Linear

variable (A : Type t) [CommRing A] [Linear A C]

/-- The syzygy-cocycle quotient is genuinely Ext², not a definition replacing Ext. -/
def cocycleQuotientEquiv [Projective U.X₂] [Projective P₁] (E : C) :
    ((K₂ ⟶ E) ⧸ LinearMap.range
      (ExtCokernel.homRestriction A (ShortComplex.mk a₂ a₁ zero) E)) ≃ₗ[A] Ext U.X₃ E 2 :=
  (ExtCokernel.homCokernelEquivExtOne A hV E).trans
    (ExtCokernel.dimensionShiftEquiv A hU E)

@[simp] theorem cocycleQuotientEquiv_mk [Projective U.X₂] [Projective P₁]
    (f : K₂ ⟶ E) :
    cocycleQuotientEquiv hU hV A E (Submodule.Quotient.mk f) = cocycleClass hU hV f := by
  simp [cocycleQuotientEquiv, ExtCokernel.homCokernelEquivExtOne,
    ExtCokernel.dimensionShiftEquiv, cocycleClass]
  rfl

section HomComplex

variable {P₂ P₃ : C} (b : P₂ ⟶ K₂) (a₃ : P₃ ⟶ P₂) (zero₃ : a₃ ≫ b = 0)

/-- Degree-two cocycles of the actual Hom complex: `a₃ ≫ f = 0`. -/
abbrev cocycles (E : C) : Submodule A (P₂ ⟶ E) :=
  LinearMap.ker (ExtCokernel.homRestriction A (ShortComplex.mk a₃ b zero₃) E)

/-- Pull a syzygy map back to an actual degree-two cocycle. -/
def syzygyToCocycle (E : C) : (K₂ ⟶ E) →ₗ[A] cocycles A b a₃ zero₃ E where
  toFun f := ⟨b ≫ f, by
    change a₃ ≫ (b ≫ f) = 0
    rw [← Category.assoc, zero₃]
    simp⟩
  map_add' f g := by apply Subtype.ext; simp
  map_smul' r f := by apply Subtype.ext; simp

omit [HasExt C] in
@[simp] theorem syzygyToCocycle_coe (f : K₂ ⟶ E) :
    (syzygyToCocycle A b a₃ zero₃ E f).val = b ≫ f := rfl

/-- Exactness at degree two identifies cocycles with maps from the second syzygy. -/
def syzygyCocycleEquiv [Epi b]
    (hW : (ShortComplex.mk a₃ b zero₃).Exact) (E : C) :
    (K₂ ⟶ E) ≃ₗ[A] cocycles A b a₃ zero₃ E :=
  LinearEquiv.ofBijective (syzygyToCocycle A b a₃ zero₃ E) ⟨by
    intro f g hfg
    exact (cancel_epi b).mp (congrArg Subtype.val hfg), by
    intro f
    exact ⟨hW.desc f.val f.property, Subtype.ext (hW.g_desc _ _)⟩⟩

/-- The degree-one coboundary map, landing in the actual cocycle submodule. -/
def coboundaryMap (E : C) : (P₁ ⟶ E) →ₗ[A] cocycles A b a₃ zero₃ E :=
  (syzygyToCocycle A b a₃ zero₃ E).comp
    (ExtCokernel.homRestriction A (ShortComplex.mk a₂ a₁ zero) E)

omit [HasExt C] in
@[simp] theorem coboundaryMap_coe (h : P₁ ⟶ E) :
    (coboundaryMap (a₂ := a₂) (a₁ := a₁) (zero := zero) A b a₃ zero₃ E h).val =
      (b ≫ a₂) ≫ h := (Category.assoc _ _ _).symm

/-- The usual degree-two cohomology of Hom: actual cocycles modulo actual coboundaries. -/
abbrev homCohomologyTwo (E : C) :=
  cocycles A b a₃ zero₃ E ⧸
    LinearMap.range (coboundaryMap (a₂ := a₂) (a₁ := a₁) (zero := zero) A b a₃ zero₃ E)

/-- The Yoneda--resolution correspondence for the actual Hom-complex cohomology. -/
def homCohomologyTwoEquivExt [Projective U.X₂] [Projective P₁] [Epi b]
    (hW : (ShortComplex.mk a₃ b zero₃).Exact) (E : C) :
    homCohomologyTwo (a₂ := a₂) (a₁ := a₁) (zero := zero) A b a₃ zero₃ E ≃ₗ[A]
      Ext U.X₃ E 2 := by
  let e := syzygyCocycleEquiv A b a₃ zero₃ hW E
  let r := ExtCokernel.homRestriction A (ShortComplex.mk a₂ a₁ zero) E
  have hm : (LinearMap.range r).map e.toLinearMap =
      LinearMap.range (coboundaryMap (a₂ := a₂) (a₁ := a₁) (zero := zero) A b a₃ zero₃ E) := by
    exact (LinearMap.range_comp r (syzygyToCocycle A b a₃ zero₃ E)).symm
  exact (Submodule.Quotient.equiv _ _ e hm).symm.trans (cocycleQuotientEquiv hU hV A E)

set_option backward.isDefEq.respectTransparency false in
@[simp] theorem homCohomologyTwoEquivExt_mk [Projective U.X₂] [Projective P₁] [Epi b]
    (hW : (ShortComplex.mk a₃ b zero₃).Exact) (f : K₂ ⟶ E) :
    homCohomologyTwoEquivExt hU hV A b a₃ zero₃ hW E
      (Submodule.Quotient.mk (syzygyToCocycle A b a₃ zero₃ E f)) =
        cocycleClass hU hV f := by
  change homCohomologyTwoEquivExt hU hV A b a₃ zero₃ hW E
    (Submodule.Quotient.mk (syzygyCocycleEquiv A b a₃ zero₃ hW E f)) = _
  simp [homCohomologyTwoEquivExt]
  exact cocycleQuotientEquiv_mk hU hV A f

end HomComplex

end Linear

end Abstract

section Syndrome

variable {A : Type u} [Ring A]
  {P F Q P₀ P₁ P₂ : Type u}
  [AddCommGroup P] [Module A P]
  [AddCommGroup F] [Module A F]
  [AddCommGroup Q] [Module A Q]
  [AddCommGroup P₀] [Module A P₀]
  [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup P₂] [Module A P₂]

/-- The full vanishing criterion for the manuscript's actual syndrome splice.
The supplied prefix is exact and its degree-zero module is projective.
Neither the syndrome cover `Q` nor the degree-one module has to be projective. -/
theorem κ_zero_iff_coboundary [Module.Projective A P₀]
    (c : Syndrome.Cochain A P F Q)
    (a₂ : P₂ →ₗ[A] P₁) (a₁ : P₁ →ₗ[A] P₀) (ε : P₀ →ₗ[A] c.C2)
    (exact21 : LinearMap.range a₂ = LinearMap.ker a₁)
    (exact10 : LinearMap.range a₁ = LinearMap.ker ε)
    (surjectiveε : Function.Surjective ε)
    (q₀ : P₀ →ₗ[A] Q) (q₁ : P₁ →ₗ[A] c.N) (f : P₂ →ₗ[A] c.C1)
    (square₀ : c.pQ.comp q₀ = ε)
    (square₁ : c.γN.comp q₁ = q₀.comp a₁)
    (square₂ : c.ι.comp f = q₁.comp a₂) :
    c.κ = 0 ↔ ∃ h : P₁ →ₗ[A] c.C1, h.comp a₂ = f := by
  let a₁Cycles : P₁ →ₗ[A] LinearMap.ker ε := a₁.codRestrict _ (by
    intro x
    rw [← exact10]
    exact ⟨x, rfl⟩)
  have a₁Cycles_surjective : Function.Surjective a₁Cycles := by
    intro z
    have hz : (z : P₀) ∈ LinearMap.range a₁ := by
      rw [exact10]
      exact z.property
    obtain ⟨x, hx⟩ := hz
    exact ⟨x, Subtype.ext hx⟩
  let a₂Cycles : P₂ →ₗ[A] LinearMap.ker a₁Cycles := a₂.codRestrict _ (by
    intro x
    apply Subtype.ext
    change a₁ (a₂ x) = 0
    have hx : a₂ x ∈ LinearMap.range a₂ := ⟨x, rfl⟩
    rw [exact21] at hx
    exact hx)
  have a₂Cycles_surjective : Function.Surjective a₂Cycles := by
    intro z
    have hz : (z : P₁) ∈ LinearMap.ker a₁ := congrArg Subtype.val z.property
    rw [← exact21] at hz
    obtain ⟨x, hx⟩ := hz
    exact ⟨x, Subtype.ext hx⟩
  let k : LinearMap.ker ε →ₗ[A] c.L :=
    (q₀.comp (LinearMap.ker ε).subtype).codRestrict _ (by
      intro z
      apply (Submodule.Quotient.mk_eq_zero _).mp
      change c.pQ (q₀ z) = 0
      exact (DFunLike.congr_fun square₀ (z : P₀)).trans z.property)
  let U := ε.shortComplexKer
  let V := a₁Cycles.shortComplexKer
  let hU : U.ShortExact := LinearMap.shortExact_shortComplexKer surjectiveε
  let hV : V.ShortExact := LinearMap.shortExact_shortComplexKer a₁Cycles_surjective
  let : Projective U.X₂ := (inferInstance : Projective (ModuleCat.of A P₀))
  let : Epi (ModuleCat.ofHom a₂Cycles) :=
    (ModuleCat.epi_iff_surjective _).mpr a₂Cycles_surjective
  let d : Comparison (U := U) (a₂ := V.f) (a₁ := V.g)
      (ModuleCat.ofHom a₂Cycles) c.first (ModuleCat.ofHom c.j) (ModuleCat.ofHom c.pQ) := {
    f₂ := ModuleCat.ofHom f
    q₁ := ModuleCat.ofHom q₁
    k := ModuleCat.ofHom k
    q₀ := ModuleCat.ofHom q₀
    square₂ := ModuleCat.hom_ext square₂
    square₁ := by
      apply ModuleCat.hom_ext
      ext x
      apply Subtype.ext
      change c.γN (q₁ x) = q₀ (a₁ x)
      exact DFunLike.congr_fun square₁ x
    square₀ := by rfl
    endpoint := ModuleCat.hom_ext square₀
  }
  have hc := d.splice_zero_iff_component hU hV c.first_shortExact c.second_shortExact
  constructor
  · intro hκ
    obtain ⟨h, hh⟩ := hc.mp hκ
    exact ⟨h.hom, ModuleCat.hom_ext_iff.mp hh⟩
  · rintro ⟨h, hh⟩
    exact hc.mpr ⟨ModuleCat.ofHom h, ModuleCat.hom_ext hh⟩

end Syndrome

end Decoupling.YonedaCocycle
