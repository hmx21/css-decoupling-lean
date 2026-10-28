import Decoupling.ExtSplitting
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The two syndrome short exact sequences

For a cochain `P --d₁→ F --γ→ Q`, this file constructs the actual quotient
`N = coker d₁`, the image `L = range γ`, and the two cohomology layers
`C1 = ker γ / range d₁`, `C2 = coker γ`. The first quotient uses the image
of `d₁` restricted to `ker γ`, so its type records the cycle condition.

Both short exact sequences of equation (18) are constructed as `ModuleCat`
short complexes and proved short exact. Their Yoneda splice `κ` is an element
of mathlib's genuine `Ext²(C2,C1)`. If `Q` is projective, `κ = 0` is equivalent
to splitting the first sequence and gives `N ≃ₗ[A] C1 × L`.

The names `C1` and `C2` deliberately refer to cohomology layers. Identifying
them with `Ext_Aⁱ(overline M_X,A)` requires the separate resolution/duality
bridge; that identification is not assumed or defined here.
-/

universe u

namespace Decoupling.Syndrome

open CategoryTheory CategoryTheory.Abelian

variable (A : Type u) [Ring A]
  (P F Q : Type u)
  [AddCommGroup P] [Module A P]
  [AddCommGroup F] [Module A F]
  [AddCommGroup Q] [Module A Q]

/-- The three-term cochain used in equation (7), with its zero composite. -/
structure Cochain where
  d₁ : P →ₗ[A] F
  γ : F →ₗ[A] Q
  square : γ.comp d₁ = 0

namespace Cochain

variable {A P F Q}
variable (c : Cochain A P F Q)

/-- The actual syndrome cokernel `N = coker d₁`. -/
abbrev N := F ⧸ LinearMap.range c.d₁

/-- The image `L = im γ`, as a submodule of `Q`. -/
abbrev L := LinearMap.range c.γ

/-- Boundaries regarded as cycles. -/
def toCycles : P →ₗ[A] LinearMap.ker c.γ :=
  c.d₁.codRestrict _ fun p => DFunLike.congr_fun c.square p

/-- First cohomology layer; no derived-functor identification is asserted. -/
abbrev C1 := LinearMap.ker c.γ ⧸ LinearMap.range c.toCycles

/-- Second cohomology layer, the actual cokernel of `γ`. -/
abbrev C2 := Q ⧸ LinearMap.range c.γ

/-- The cochain bundled as a short complex in the module category. -/
def complex : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.moduleCatMk c.d₁ c.γ c.square

/-- The quotient `C1` is canonically the categorical homology of this cochain. -/
noncomputable def homologyIsoC1 :
    c.complex.homology ≅ ModuleCat.of A c.C1 :=
  c.complex.moduleCatHomologyIso

/-- The canonical augmentation `F → N`. -/
abbrev ε : F →ₗ[A] c.N := (LinearMap.range c.d₁).mkQ

/-- Inclusion of the image into the cover Q; this definition does not require freeness. -/
abbrev j : c.L →ₗ[A] Q := (LinearMap.range c.γ).subtype

/-- Quotient map from the cover to the second cohomology layer. -/
abbrev pQ : Q →ₗ[A] c.C2 := (LinearMap.range c.γ).mkQ

/-- The map `N → L` induced by `γ`. -/
def π : c.N →ₗ[A] c.L :=
  (LinearMap.range c.d₁).liftQ c.γ.rangeRestrict (by
    rintro _ ⟨p, rfl⟩
    apply Subtype.ext
    exact DFunLike.congr_fun c.square p)

/-- The inclusion of first cohomology into the syndrome cokernel. -/
def ι : c.C1 →ₗ[A] c.N :=
  (LinearMap.range c.toCycles).liftQ
    (c.ε.comp (LinearMap.ker c.γ).subtype) (by
      rintro _ ⟨p, rfl⟩
      change (Submodule.Quotient.mk (c.d₁ p) : c.N) = 0
      exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨p, rfl⟩)

@[simp] theorem π_mk (v : F) : c.π (c.ε v) = c.γ.rangeRestrict v := rfl

@[simp] theorem ι_mk (v : LinearMap.ker c.γ) :
    c.ι ((LinearMap.range c.toCycles).mkQ v) = c.ε v := rfl

/-- The induced map still agrees with `γ` after composing with the augmentation. -/
theorem j_π_ε : c.j.comp (c.π.comp c.ε) = c.γ := by
  ext v
  rfl

/-- The induced map `γ_N:N→Q` from equation (18). -/
def γN : c.N →ₗ[A] Q := c.j.comp c.π

@[simp] theorem γN_mk (v : F) : c.γN (c.ε v) = c.γ v := rfl

theorem ι_injective : Function.Injective c.ι := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨v, rfl⟩ := (LinearMap.range c.toCycles).mkQ_surjective x
  have hv : (v : F) ∈ LinearMap.range c.d₁ :=
    (Submodule.Quotient.mk_eq_zero _).mp hx
  obtain ⟨p, hp⟩ := hv
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  exact ⟨p, Subtype.ext hp⟩

theorem π_surjective : Function.Surjective c.π := by
  intro l
  obtain ⟨v, hv⟩ := c.γ.surjective_rangeRestrict l
  exact ⟨c.ε v, hv⟩

theorem π_ι : c.π.comp c.ι = 0 := by
  apply Submodule.linearMap_qext
  ext v
  exact v.property

/-- The actual first short complex `C1 → N → L`. -/
def first : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.moduleCatMk c.ι c.π c.π_ι

theorem first_shortExact : c.first.ShortExact where
  exact := by
    apply (c.first.moduleCat_exact_iff).mpr
    intro n hn
    obtain ⟨v, rfl⟩ := (LinearMap.range c.d₁).mkQ_surjective n
    have hv : c.γ v = 0 := congrArg Subtype.val hn
    exact ⟨(LinearMap.range c.toCycles).mkQ ⟨v, hv⟩, rfl⟩
  mono_f := (ModuleCat.mono_iff_injective _).mpr c.ι_injective
  epi_g := (ModuleCat.epi_iff_surjective _).mpr c.π_surjective

theorem pQ_j : c.pQ.comp c.j = 0 := by
  ext l
  exact (Submodule.Quotient.mk_eq_zero _).mpr l.property

/-- The actual second short complex `L → Q → C2`. -/
def second : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.moduleCatMk c.j c.pQ c.pQ_j

theorem second_shortExact : c.second.ShortExact where
  exact := by
    apply (c.second.moduleCat_exact_iff).mpr
    intro q hq
    exact ⟨⟨q, (Submodule.Quotient.mk_eq_zero _).mp hq⟩, rfl⟩
  mono_f := (ModuleCat.mono_iff_injective _).mpr (LinearMap.range c.γ).injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (LinearMap.range c.γ).mkQ_surjective

/-- The obstruction class is the genuine Yoneda splice in `Ext²(C2,C1)`. -/
noncomputable def κ : Ext (ModuleCat.of A c.C2) (ModuleCat.of A c.C1) 2 :=
  c.second_shortExact.extClass.comp c.first_shortExact.extClass (by decide : 1 + 1 = 2)

/-- Proposition III.1 for the actual two quotient sequences, before the
cohomology-to-Ext-layer identification. Projectivity of the cover suffices. -/
theorem κ_zero_iff_splitting [Module.Projective A Q] :
    c.κ = 0 ↔ Nonempty c.first.Splitting := by
  exact ExtSplitting.splice_zero_iff_splitting c.first_shortExact
    (ModuleCat.ofHom c.j) (ModuleCat.ofHom c.pQ)
    (ModuleCat.hom_ext c.pQ_j) c.second_shortExact

/-- The splitting criterion stated using an ordinary module-linear section. -/
theorem κ_zero_iff_section [Module.Projective A Q] :
    c.κ = 0 ↔ ∃ σ : c.L →ₗ[A] c.N, c.π.comp σ = LinearMap.id := by
  let : Projective c.second.X₂ :=
    (inferInstance : Projective (ModuleCat.of A Q))
  have hclass : c.κ = 0 ↔ c.first_shortExact.extClass = 0 :=
    ExtSplitting.dimensionShift_zero_iff c.second_shortExact c.first_shortExact.extClass
  rw [hclass, ExtSplitting.extClass_zero_iff_section c.first_shortExact]
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ.hom, ModuleCat.hom_ext_iff.mp hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨ModuleCat.ofHom σ, ModuleCat.hom_ext hσ⟩

/-- Vanishing of the genuine splice gives the syndrome direct-sum decomposition.
The finite product is the underlying module of the manuscript's binary direct sum. -/
noncomputable def equivProdOfκZero [Module.Projective A Q] (h : c.κ = 0) :
    c.N ≃ₗ[A] (c.C1 × c.L) :=
  ExtSplitting.moduleEquivProd c.first_shortExact
    ((ExtSplitting.extClass_zero_iff_splitting c.first_shortExact).mpr
      ((c.κ_zero_iff_splitting).mp h))

end Cochain

end Decoupling.Syndrome
