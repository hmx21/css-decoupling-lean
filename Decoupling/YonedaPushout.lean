import Decoupling.YonedaCocycle
import Decoupling.Comparison

/-!
# The manuscript's literal fixed-endpoint pushout

For `K₂ = ker a₁` and `f̄ : K₂ → E`, this module constructs exactly
`W_f = (E × P₁) / range (k ↦ (f̄ k,k))`, using the manuscript's
characteristic-two signs. Its injection, relation map and universal comparison
map are actual quotient maps. The represented class is mathlib's genuine Ext.
-/

namespace Decoupling.YonedaPushout

open CategoryTheory CategoryTheory.Abelian

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {A : Type} [CommRing A]
  {E P₁ P₀ : Type} [AddCommGroup E] [Module A E]
  [AddCommGroup P₁] [Module A P₁] [AddCommGroup P₀] [Module A P₀]

variable (a₁ : P₁ →ₗ[A] P₀) (f : LinearMap.ker a₁ →ₗ[A] E)

def graph : LinearMap.ker a₁ →ₗ[A] E × P₁ := f.prod (LinearMap.ker a₁).subtype
def relations : Submodule A (E × P₁) := LinearMap.range (graph a₁ f)
abbrev W := (E × P₁) ⧸ relations a₁ f
abbrev mk : E × P₁ →ₗ[A] W a₁ f := (relations a₁ f).mkQ
def ι : E →ₗ[A] W a₁ f := (mk a₁ f).comp (LinearMap.inl A E P₁)
def j : P₁ →ₗ[A] W a₁ f := (mk a₁ f).comp (LinearMap.inr A E P₁)

def δ : W a₁ f →ₗ[A] P₀ := (relations a₁ f).liftQ
    (a₁.comp (LinearMap.snd A E P₁)) (by
      rintro _ ⟨k, rfl⟩
      exact k.property)

@[simp] theorem δ_mk (e : E) (z : P₁) : δ a₁ f (mk a₁ f (e, z)) = a₁ z := rfl
@[simp] theorem δ_ι (e : E) : δ a₁ f (ι a₁ f e) = 0 := map_zero a₁
@[simp] theorem δ_j (z : P₁) : δ a₁ f (j a₁ f z) = a₁ z := rfl

theorem mk_graph (k : LinearMap.ker a₁) : mk a₁ f (f k, k.val) = 0 :=
  (Submodule.Quotient.mk_eq_zero _).mpr ⟨k, rfl⟩

/-- Every quotient representative is the sum of the two structural maps. -/
theorem mk_eq_ι_add_j (e : E) (z : P₁) :
    mk a₁ f (e, z) = ι a₁ f e + j a₁ f z := by
  change mk a₁ f (e, z) = mk a₁ f (e, 0) + mk a₁ f (0, z)
  simpa only [Prod.mk_add_mk, add_zero, zero_add] using map_add (mk a₁ f) (e, 0) (0, z)

theorem ι_injective : Function.Injective (ι a₁ f) := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro e he
  obtain ⟨k, hk⟩ := (Submodule.Quotient.mk_eq_zero _).mp he
  have hk₀ : k = 0 := Subtype.ext (congrArg Prod.snd hk)
  subst k
  exact (congrArg Prod.fst hk).symm.trans (map_zero f)

variable [CharP A 2]

/-- The quotient relation reduces a cycle representative exactly as in II.B. -/
theorem cycle_reduce (e : E) (k : LinearMap.ker a₁) :
    ι a₁ f (e + f k) = mk a₁ f (e, k.val) := by
  have hsum : (e, k.val) + (f k, k.val) = (e + f k, 0) := by
    apply Prod.ext
    · rfl
    · exact Comparison.module_add_self (A := A) P₁ k.val
  calc
    ι a₁ f (e + f k) = mk a₁ f ((e, k.val) + (f k, k.val)) := congrArg (mk a₁ f) hsum.symm
    _ = mk a₁ f (e, k.val) := by rw [map_add, mk_graph, add_zero]

/-- The defining square of the literal pushout. -/
theorem ι_f_eq_j (k : LinearMap.ker a₁) : ι a₁ f (f k) = j a₁ f k := by
  change ι a₁ f (f k) = mk a₁ f (0, k.val)
  simpa only [zero_add] using cycle_reduce a₁ f 0 k

theorem range_ι_eq_ker_δ : LinearMap.range (ι a₁ f) = LinearMap.ker (δ a₁ f) := by
  apply Submodule.ext
  intro w
  constructor
  · rintro ⟨e, rfl⟩
    exact δ_ι a₁ f e
  · intro hw
    obtain ⟨⟨e, z⟩, rfl⟩ := (relations a₁ f).mkQ_surjective w
    exact ⟨e + f ⟨z, hw⟩, cycle_reduce a₁ f e ⟨z, hw⟩⟩

omit [CharP A 2] in
theorem range_δ : LinearMap.range (δ a₁ f) = LinearMap.range a₁ := by
  apply Submodule.ext
  intro x
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨⟨e, z⟩, rfl⟩ := (relations a₁ f).mkQ_surjective w
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨j a₁ f z, rfl⟩

def δRange : W a₁ f →ₗ[A] LinearMap.range a₁ := (δ a₁ f).codRestrict _ (by
  intro w
  rw [← range_δ a₁ f]
  exact ⟨w, rfl⟩)

omit [CharP A 2] in
theorem δRange_surjective : Function.Surjective (δRange a₁ f) := by
  intro x
  obtain ⟨z, hz⟩ := x.property
  exact ⟨j a₁ f z, Subtype.ext hz⟩

theorem range_ι_eq_ker_δRange : LinearMap.range (ι a₁ f) = LinearMap.ker (δRange a₁ f) := by
  rw [range_ι_eq_ker_δ]
  apply Submodule.ext
  intro w
  constructor
  · intro hw
    exact Subtype.ext hw
  · intro hw
    exact congrArg Subtype.val hw

def first : ShortComplex (ModuleCat A) := ShortComplex.moduleCatMk
  (ι a₁ f) (δRange a₁ f) (by
    apply LinearMap.ext
    intro e
    apply Subtype.ext
    exact δ_ι a₁ f e)

theorem first_shortExact : (first a₁ f).ShortExact where
  exact := (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr (range_ι_eq_ker_δRange a₁ f)
  mono_f := (ModuleCat.mono_iff_injective _).mpr (ι_injective a₁ f)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (δRange_surjective a₁ f)

section Universal

variable {N : Type} [AddCommGroup N] [Module A N]
variable (i : E →ₗ[A] N) (q : P₁ →ₗ[A] N)
variable (h : i.comp f = q.comp (LinearMap.ker a₁).subtype)

/-- The literal universal map Φ_f[e,z]=i(e)+q(z). -/
def desc : W a₁ f →ₗ[A] N := (relations a₁ f).liftQ (i.coprod q) (by
  rintro _ ⟨k, rfl⟩
  change i (f k) + q k.val = 0
  rw [show i (f k) = q k.val from DFunLike.congr_fun h k]
  exact Comparison.module_add_self (A := A) N _)

@[simp] theorem desc_mk (e : E) (z : P₁) :
    desc a₁ f i q h (mk a₁ f (e, z)) = i e + q z := rfl

@[simp] theorem desc_ι (e : E) : desc a₁ f i q h (ι a₁ f e) = i e := by
  change i e + q 0 = i e
  rw [map_zero, add_zero]

@[simp] theorem desc_j (z : P₁) : desc a₁ f i q h (j a₁ f z) = q z := by
  change i 0 + q z = q z
  rw [map_zero, zero_add]

/-- Uniqueness proves the actual pushout universal property. -/
theorem desc_unique (g : W a₁ f →ₗ[A] N)
    (hi : g.comp (ι a₁ f) = i) (hq : g.comp (j a₁ f) = q) : g = desc a₁ f i q h := by
  apply LinearMap.ext
  intro w
  obtain ⟨⟨e, z⟩, rfl⟩ := (relations a₁ f).mkQ_surjective w
  rw [mk_eq_ι_add_j, map_add]
  rw [show g (ι a₁ f e) = i e from DFunLike.congr_fun hi e,
    show g (j a₁ f z) = q z from DFunLike.congr_fun hq z]
  simp only [map_add, desc_ι, desc_j]

end Universal

section Extension

variable {B : Type} [AddCommGroup B] [Module A B]
variable (ε : P₀ →ₗ[A] B)
variable (hexact : LinearMap.range a₁ = LinearMap.ker ε)
variable (hsurj : Function.Surjective ε)

def second : ShortComplex (ModuleCat A) := ShortComplex.moduleCatMk
  (LinearMap.range a₁).subtype ε (by
    apply LinearMap.ext
    intro x
    have hx : (x : P₀) ∈ LinearMap.ker ε := by rw [← hexact]; exact x.property
    exact hx)

omit [CharP A 2] in
include hsurj in
theorem second_shortExact : (second a₁ ε hexact).ShortExact where
  exact := by
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [hexact]
    exact hx
  mono_f := (ModuleCat.mono_iff_injective _).mpr (LinearMap.range a₁).injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr hsurj

def syzygy : ShortComplex (ModuleCat A) := ShortComplex.moduleCatMk
  (LinearMap.ker a₁).subtype a₁.rangeRestrict (by
    apply LinearMap.ext
    intro x
    exact Subtype.ext x.property)

omit [CharP A 2] in
theorem syzygy_shortExact : (syzygy a₁).ShortExact where
  exact := by
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    exact ⟨⟨x, congrArg Subtype.val hx⟩, rfl⟩
  mono_f := (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker a₁).injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr a₁.surjective_rangeRestrict

/-- The literal W_f two-extension represents a genuine derived Ext² class. -/
def extClass : Ext (ModuleCat.of A B) (ModuleCat.of A E) 2 :=
  (second_shortExact a₁ ε hexact hsurj).extClass.comp
    (first_shortExact a₁ f).extClass (by decide)

/-- Its class is exactly the cocycle class of f̄ on the actual second syzygy. -/
theorem extClass_eq_cocycleClass : extClass a₁ f ε hexact hsurj =
    YonedaCocycle.cocycleClass (second_shortExact a₁ ε hexact hsurj)
      (syzygy_shortExact a₁) (ModuleCat.ofHom f) := by
  symm
  apply YonedaCocycle.cocycleClass_eq_splice
    (second_shortExact a₁ ε hexact hsurj) (syzygy_shortExact a₁)
    (first_shortExact a₁ f) (second_shortExact a₁ ε hexact hsurj)
    (ModuleCat.ofHom f) (ModuleCat.ofHom (j a₁ f)) (𝟙 _) (𝟙 _)
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact ι_f_eq_j a₁ f
  · rfl
  · rfl
  · rfl

include hsurj in
/-- The vanishing criterion for this literal quotient model, using genuine Ext. -/
theorem extClass_zero_iff [Module.Projective A P₀] :
    extClass a₁ f ε hexact hsurj = 0 ↔
      ∃ h : P₁ →ₗ[A] E, h.comp (LinearMap.ker a₁).subtype = f := by
  let : Projective (second a₁ ε hexact).X₂ :=
    inferInstanceAs (Projective (ModuleCat.of A P₀))
  rw [extClass_eq_cocycleClass, YonedaCocycle.cocycleClass_zero_iff
    (second_shortExact a₁ ε hexact hsurj) (syzygy_shortExact a₁) (ModuleCat.ofHom f)]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h.hom, ModuleCat.hom_ext_iff.mp hh⟩
  · rintro ⟨h, hh⟩
    exact ⟨ModuleCat.ofHom h, ModuleCat.hom_ext hh⟩

end Extension

section Coboundary

variable (h : P₁ →ₗ[A] E)

/-- The explicit characteristic-two shear underlying Ψ_h. -/
def shear : (E × P₁) ≃ₗ[A] (E × P₁) where
  toFun x := (x.1 + h x.2, x.2)
  invFun x := (x.1 + h x.2, x.2)
  left_inv x := by
    apply Prod.ext
    · change x.1 + h x.2 + h x.2 = x.1
      rw [add_assoc, Comparison.module_add_self (A := A) E, add_zero]
    · rfl
  right_inv x := by
    apply Prod.ext
    · change x.1 + h x.2 + h x.2 = x.1
      rw [add_assoc, Comparison.module_add_self (A := A) E, add_zero]
    · rfl
  map_add' x y := by
    apply Prod.ext
    · change x.1 + y.1 + h (x.2 + y.2) = (x.1 + h x.2) + (y.1 + h y.2)
      rw [map_add]
      abel
    · rfl
  map_smul' r x := by
    apply Prod.ext
    · change r • x.1 + h (r • x.2) = r • (x.1 + h x.2)
      rw [map_smul, smul_add]
    · rfl

variable (g : LinearMap.ker a₁ →ₗ[A] E)
variable (hfg : f + h.comp (LinearMap.ker a₁).subtype = g)

include hfg in
theorem shear_relations : (relations a₁ f).map (shear h).toLinearMap = relations a₁ g := by
  apply Submodule.ext
  intro x
  constructor
  · rintro ⟨_, ⟨k, rfl⟩, rfl⟩
    refine ⟨k, ?_⟩
    apply Prod.ext
    · exact (DFunLike.congr_fun hfg k).symm
    · rfl
  · rintro ⟨k, rfl⟩
    refine ⟨graph a₁ f k, ⟨k, rfl⟩, ?_⟩
    apply Prod.ext
    · exact DFunLike.congr_fun hfg k
    · rfl

/-- The manuscript's explicit isomorphism `[e,z]_f ↦ [e+h(z),z]_g`. -/
def coboundaryEquiv : W a₁ f ≃ₗ[A] W a₁ g :=
  Submodule.Quotient.equiv _ _ (shear h) (shear_relations a₁ f h g hfg)

@[simp] theorem coboundaryEquiv_mk (e : E) (z : P₁) :
    coboundaryEquiv a₁ f h g hfg (mk a₁ f (e, z)) = mk a₁ g (e + h z, z) := rfl

@[simp] theorem coboundaryEquiv_symm_mk (e : E) (z : P₁) :
    (coboundaryEquiv a₁ f h g hfg).symm (mk a₁ g (e, z)) =
      mk a₁ f (e + h z, z) := rfl

/-- Ψ_h fixes the left endpoint. -/
theorem coboundaryEquiv_ι (e : E) :
    coboundaryEquiv a₁ f h g hfg (ι a₁ f e) = ι a₁ g e := by
  change mk a₁ g (e + h 0, 0) = mk a₁ g (e, 0)
  rw [map_zero, add_zero]

/-- Ψ_h fixes the right-hand free module of the two-extension. -/
theorem δ_coboundaryEquiv :
    (δ a₁ g).comp (coboundaryEquiv a₁ f h g hfg).toLinearMap = δ a₁ f := by
  apply LinearMap.ext
  intro w
  obtain ⟨⟨e, z⟩, rfl⟩ := (relations a₁ f).mkQ_surjective w
  rfl

end Coboundary

section ZeroModel

/-- The literal projection `pr₁[e,z]_0=e` in the zero pushout model. -/
def zeroProjection : W a₁ (0 : LinearMap.ker a₁ →ₗ[A] E) →ₗ[A] E :=
  desc a₁ 0 LinearMap.id 0 (by ext k; rfl)

@[simp] theorem zeroProjection_mk (e : E) (z : P₁) :
    zeroProjection a₁ (mk a₁ 0 (e, z)) = e := by
  change e + 0 = e
  exact add_zero e

def zeroCoordinates : W a₁ (0 : LinearMap.ker a₁ →ₗ[A] E) →ₗ[A]
    E × LinearMap.range a₁ := (zeroProjection a₁).prod (δRange a₁ 0)

theorem zeroCoordinates_bijective : Function.Bijective (zeroCoordinates (E := E) a₁) := by
  constructor
  · apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    have hz : w ∈ LinearMap.ker (δRange a₁ (0 : LinearMap.ker a₁ →ₗ[A] E)) :=
      congrArg Prod.snd hw
    rw [← range_ι_eq_ker_δRange] at hz
    obtain ⟨e, rfl⟩ := hz
    have he : zeroProjection a₁ (mk a₁ 0 (e, 0)) = 0 := congrArg Prod.fst hw
    rw [zeroProjection_mk] at he
    rw [he, map_zero]
  · rintro ⟨e, z⟩
    obtain ⟨v, hv⟩ := z.property
    refine ⟨mk a₁ 0 (e, v), Prod.ext (zeroProjection_mk a₁ e v) (Subtype.ext hv)⟩

/-- The exact displayed W₀≃E⊕ker ε identification, since range a₁=ker ε. -/
def zeroEquiv : W a₁ (0 : LinearMap.ker a₁ →ₗ[A] E) ≃ₗ[A] E × LinearMap.range a₁ :=
  LinearEquiv.ofBijective (zeroCoordinates a₁) (zeroCoordinates_bijective a₁)

@[simp] theorem zeroEquiv_mk (e : E) (z : P₁) :
    zeroEquiv a₁ (mk a₁ 0 (e, z)) = (e, a₁.rangeRestrict z) := by
  apply Prod.ext
  · exact zeroProjection_mk a₁ e z
  · rfl

end ZeroModel

section FixedEndpointMaps

variable {B N Q : Type} [AddCommGroup B] [Module A B]
  [AddCommGroup N] [Module A N] [AddCommGroup Q] [Module A Q]
variable (ε : P₀ →ₗ[A] B) (i : E →ₗ[A] N) (γ : N →ₗ[A] Q) (p : Q →ₗ[A] B)
variable (q₁ : P₁ →ₗ[A] N) (q₀ : P₀ →ₗ[A] Q)
variable (hf : i.comp f = q₁.comp (LinearMap.ker a₁).subtype)

/-- The three literal fixed-endpoint squares of E_f→E, with Φ_f as the
actual quotient-induced map and q₀ as its degree-zero component. -/
theorem fixed_endpoint_squares (hγi : γ.comp i = 0)
    (hγq : γ.comp q₁ = q₀.comp a₁) (hpq : p.comp q₀ = ε) :
    (desc a₁ f i q₁ hf).comp (ι a₁ f) = i ∧
    γ.comp (desc a₁ f i q₁ hf) = q₀.comp (δ a₁ f) ∧ p.comp q₀ = ε := by
  refine ⟨?_, ?_, hpq⟩
  · apply LinearMap.ext
    exact desc_ι a₁ f i q₁ hf
  · apply LinearMap.ext
    intro w
    obtain ⟨⟨e, z⟩, rfl⟩ := (relations a₁ f).mkQ_surjective w
    change γ (i e + q₁ z) = q₀ (a₁ z)
    rw [map_add, show γ (i e) = 0 from DFunLike.congr_fun hγi e,
      zero_add]
    exact DFunLike.congr_fun hγq z

/-- The two nontrivial squares of E₀→T₀ are literally pr₁ι₀=id and εδ₀=0. -/
theorem zero_endpoint_squares (hexact : LinearMap.range a₁ = LinearMap.ker ε) :
    (zeroProjection (E := E) a₁).comp (ι a₁ 0) = LinearMap.id ∧
    ε.comp (δ a₁ (0 : LinearMap.ker a₁ →ₗ[A] E)) = 0 := by
  constructor
  · apply LinearMap.ext
    intro e
    exact zeroProjection_mk a₁ e 0
  · apply LinearMap.ext
    intro w
    obtain ⟨⟨e, z⟩, rfl⟩ := (relations a₁ (0 : LinearMap.ker a₁ →ₗ[A] E)).mkQ_surjective w
    have hz : a₁ z ∈ LinearMap.ker ε := by rw [← hexact]; exact ⟨z, rfl⟩
    exact hz

end FixedEndpointMaps

section ZeroZigzag

variable {B : Type} [AddCommGroup B] [Module A B]
variable (ε : P₀ →ₗ[A] B) (hexact : LinearMap.range a₁ = LinearMap.ker ε)

/-- W₀ is literally E⊕ker ε under exactness of the source prefix. -/
def zeroEquivKer : W a₁ (0 : LinearMap.ker a₁ →ₗ[A] E) ≃ₗ[A]
    E × LinearMap.ker ε :=
  (zeroEquiv a₁).trans
    (LinearEquiv.prodCongr (LinearEquiv.refl A E) (LinearEquiv.ofEq _ _ hexact))

include hexact in
/-- The explicit isomorphism E_f≅E₀ when f=h|ker a₁, with both fixed-endpoint
squares and the literal maps from E₀ to the zero extension. -/
theorem zero_zigzag (h : P₁ →ₗ[A] E)
    (hf : h.comp (LinearMap.ker a₁).subtype = f) :
    ∃ Ψ : W a₁ f ≃ₗ[A] W a₁ (0 : LinearMap.ker a₁ →ₗ[A] E),
      (∀ e z, Ψ (mk a₁ f (e, z)) = mk a₁ 0 (e + h z, z)) ∧
      (∀ e, Ψ (ι a₁ f e) = ι a₁ 0 e) ∧
      (δ a₁ 0).comp Ψ.toLinearMap = δ a₁ f ∧
      (zeroProjection (E := E) a₁).comp (ι a₁ 0) = LinearMap.id ∧
      ε.comp (δ a₁ (0 : LinearMap.ker a₁ →ₗ[A] E)) = 0 := by
  have hf0 : f + h.comp (LinearMap.ker a₁).subtype = 0 := by
    rw [hf]
    apply LinearMap.ext
    intro k
    exact Comparison.module_add_self (A := A) E (f k)
  refine ⟨coboundaryEquiv a₁ f h 0 hf0, coboundaryEquiv_mk a₁ f h 0 hf0,
    coboundaryEquiv_ι a₁ f h 0 hf0, δ_coboundaryEquiv a₁ f h 0 hf0, ?_⟩
  exact zero_endpoint_squares a₁ ε hexact

end ZeroZigzag

section CocycleDescent

variable {P₂ P₃ : Type} [AddCommGroup P₂] [Module A P₂]
  [AddCommGroup P₃] [Module A P₃]
variable (a₂ : P₂ →ₗ[A] P₁) (exact21 : LinearMap.range a₂ = LinearMap.ker a₁)

/-- The differential onto the actual second syzygy K₂=ker a₁. -/
def toKernel : P₂ →ₗ[A] LinearMap.ker a₁ := a₂.codRestrict _ (by
  intro x
  rw [← exact21]
  exact ⟨x, rfl⟩)

omit [CharP A 2] in
theorem toKernel_surjective : Function.Surjective (toKernel a₁ a₂ exact21) := by
  intro k
  have hk : (k : P₁) ∈ LinearMap.range a₂ := by rw [exact21]; exact k.property
  obtain ⟨x, hx⟩ := hk
  exact ⟨x, Subtype.ext hx⟩

omit [CharP A 2] in
/-- Starting with a genuine degree-two cocycle constructs f̄, rather than
assuming that the cocycle has already descended through the syzygy quotient. -/
theorem exists_bar_of_cocycle (a₃ : P₃ →ₗ[A] P₂)
    (exact32 : LinearMap.range a₃ = LinearMap.ker a₂)
    (f₂ : P₂ →ₗ[A] E) (hcocycle : f₂.comp a₃ = 0) :
    ∃ f : LinearMap.ker a₁ →ₗ[A] E, f.comp (toKernel a₁ a₂ exact21) = f₂ := by
  apply ZeroComparison.exists_descend_of_surjective
    (toKernel a₁ a₂ exact21) (toKernel_surjective a₁ a₂ exact21) f₂
  intro x hx
  have hx' : x ∈ LinearMap.ker a₂ := congrArg Subtype.val hx
  rw [← exact32] at hx'
  obtain ⟨y, rfl⟩ := hx'
  exact DFunLike.congr_fun hcocycle y

/-- The canonical comparison into W_f recovers the original degree-two
component on every representative a₂y. -/
theorem recovered_component (f₂ : P₂ →ₗ[A] E)
    (hf : f.comp (toKernel a₁ a₂ exact21) = f₂) :
    (ι a₁ f).comp f₂ = (j a₁ f).comp a₂ := by
  apply LinearMap.ext
  intro y
  change ι a₁ f (f₂ y) = j a₁ f (a₂ y)
  rw [← DFunLike.congr_fun hf y]
  exact ι_f_eq_j a₁ f (toKernel a₁ a₂ exact21 y)

end CocycleDescent

section SyndromeComparison

variable {P F Q : Type} [AddCommGroup P] [Module A P]
  [AddCommGroup F] [Module A F] [AddCommGroup Q] [Module A Q]
variable (c : Syndrome.Cochain A P F Q)
variable (f : LinearMap.ker a₁ →ₗ[A] c.C1)
variable (ε : P₀ →ₗ[A] c.C2) (hexact : LinearMap.range a₁ = LinearMap.ker ε)
variable (hsurj : Function.Surjective ε)
variable (q₁ : P₁ →ₗ[A] c.N) (q₀ : P₀ →ₗ[A] Q)
variable (hf : c.ι.comp f = q₁.comp (LinearMap.ker a₁).subtype)
variable (h₁ : c.γN.comp q₁ = q₀.comp a₁) (h₀ : c.pQ.comp q₀ = ε)

include hf h₁ h₀ in
/-- The actual literal pushout two-extension has the same genuine class κ
as the supplied physical extension. This is the fixed-endpoint Φ_f diagram. -/
theorem extClass_eq_κ : extClass a₁ f ε hexact hsurj = c.κ := by
  have hk : LinearMap.ker a₁.rangeRestrict ≤ LinearMap.ker (c.π.comp q₁) := by
    intro x hx
    have hx' : x ∈ LinearMap.ker a₁ := congrArg Subtype.val hx
    have hi : c.ι (f ⟨x, hx'⟩) = q₁ x := DFunLike.congr_fun hf ⟨x, hx'⟩
    change c.π (q₁ x) = 0
    rw [← hi]
    exact DFunLike.congr_fun c.π_ι (f ⟨x, hx'⟩)
  obtain ⟨k, hk⟩ := ZeroComparison.exists_descend_of_surjective
    a₁.rangeRestrict a₁.surjective_rangeRestrict (c.π.comp q₁) hk
  have hk₀ : c.j.comp k = q₀.comp (LinearMap.range a₁).subtype := by
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := a₁.surjective_rangeRestrict z
    change c.j (k (a₁.rangeRestrict x)) = q₀ (a₁ x)
    rw [show k (a₁.rangeRestrict x) = c.π (q₁ x) from DFunLike.congr_fun hk x]
    exact DFunLike.congr_fun h₁ x
  rw [extClass_eq_cocycleClass]
  exact YonedaCocycle.cocycleClass_eq_splice
    (second_shortExact a₁ ε hexact hsurj) (syzygy_shortExact a₁)
    c.first_shortExact c.second_shortExact (ModuleCat.ofHom f)
    (ModuleCat.ofHom q₁) (ModuleCat.ofHom k) (ModuleCat.ofHom q₀)
    (ModuleCat.hom_ext hf) (ModuleCat.hom_ext hk.symm)
    (ModuleCat.hom_ext hk₀) (ModuleCat.hom_ext h₀)

end SyndromeComparison

end
end Decoupling.YonedaPushout
