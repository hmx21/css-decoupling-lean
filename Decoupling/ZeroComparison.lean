import Decoupling.Syndrome
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# Zero degree-two comparison component kills the genuine splice

This is the zero-component step in the proof of Theorem II.1, expressed using
mathlib's genuine Ext classes and their naturality. It does not define a
separate model of Yoneda equivalence. A comparison from an exact presentation
whose degree-one map kills all degree-two boundaries descends to its cycles.
That descent lifts the first extension and forces the two-extension class to
vanish. A projective cover then gives the syndrome splitting.
-/

universe w v u

namespace Decoupling.ZeroComparison

open CategoryTheory CategoryTheory.Abelian

section Abstract

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- An identity-endpoint comparison into the second short exact sequence kills
the splice if its left component lifts through the first sequence. This is
the naturality step; none of the middle objects needs to be projective. -/
theorem splice_zero_of_lifted_comparison
    {S U : ShortComplex C} (hS : S.ShortExact) (hU : U.ShortExact)
    {Q : C} (j : S.X₃ ⟶ Q) (p : Q ⟶ U.X₃) (hjp : j ≫ p = 0)
    (hT : (ShortComplex.mk j p hjp).ShortExact)
    (k : U.X₁ ⟶ S.X₃) (q₀ : U.X₂ ⟶ Q)
    (left_square : k ≫ j = U.f ≫ q₀) (right_square : q₀ ≫ p = U.g)
    (h : U.X₁ ⟶ S.X₂) (lift_eq : h ≫ S.g = k) :
    hT.extClass.comp hS.extClass (by decide : 1 + 1 = 2) = 0 := by
  let f : U ⟶ ShortComplex.mk j p hjp := {
    τ₁ := k
    τ₂ := q₀
    τ₃ := 𝟙 U.X₃
    comm₁₂ := left_square
    comm₂₃ := by simpa only [Category.comp_id] using right_square
  }
  have natural : hU.extClass.comp (Ext.mk₀ k) (add_zero 1) = hT.extClass := by
    simpa only [f, Ext.mk₀_id_comp] using hU.extClass_naturality hT f
  have zero : (Ext.mk₀ k).comp hS.extClass (zero_add 1) = 0 := by
    rw [← lift_eq, ← Ext.mk₀_comp_mk₀_assoc, hS.comp_extClass, Ext.comp_zero]
  rw [← natural, Ext.comp_assoc_of_second_deg_zero, zero, Ext.comp_zero]

end Abstract

section Descent

variable {A : Type u} [Ring A]
  {M K N : Type u}
  [AddCommGroup M] [Module A M]
  [AddCommGroup K] [Module A K]
  [AddCommGroup N] [Module A N]

/-- Descent through a surjective module map, proved with the actual kernel quotient. -/
theorem exists_descend_of_surjective (f : M →ₗ[A] K) (hf : Function.Surjective f)
    (g : M →ₗ[A] N) (hker : LinearMap.ker f ≤ LinearMap.ker g) :
    ∃ h : K →ₗ[A] N, h.comp f = g := by
  let h := ((LinearMap.ker f).liftQ g hker).comp
    (f.quotKerEquivOfSurjective hf).symm.toLinearMap
  refine ⟨h, ?_⟩
  ext x
  simp only [h, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]

end Descent

section Syndrome

variable {A : Type u} [Ring A]
  {P F Q P₀ P₁ P₂ : Type u}
  [AddCommGroup P] [Module A P]
  [AddCommGroup F] [Module A F]
  [AddCommGroup Q] [Module A Q]
  [AddCommGroup P₀] [Module A P₀]
  [AddCommGroup P₁] [Module A P₁]
  [AddCommGroup P₂] [Module A P₂]

/-- The zero degree-two comparison case used in Theorem II.1.

The source prefix `P₂ → P₁ → P₀ → C2 → 0` is exact at `P₁`, `P₀`, and `C2`.
The two comparison squares commute, and the degree-one comparison `q₁` kills
`a₂`, which is exactly the zero-component condition. These data force the
genuine splice class to vanish. No projectivity or freeness is needed here.
-/
theorem κ_eq_zero_of_zero_component (c : Syndrome.Cochain A P F Q)
    (a₂ : P₂ →ₗ[A] P₁) (a₁ : P₁ →ₗ[A] P₀) (ε : P₀ →ₗ[A] c.C2)
    (exact21 : LinearMap.range a₂ = LinearMap.ker a₁)
    (exact10 : LinearMap.range a₁ = LinearMap.ker ε)
    (surjectiveε : Function.Surjective ε)
    (q₀ : P₀ →ₗ[A] Q) (q₁ : P₁ →ₗ[A] c.N)
    (square₀ : c.pQ.comp q₀ = ε)
    (square₁ : c.γN.comp q₁ = q₀.comp a₁)
    (zero_component : q₁.comp a₂ = 0) : c.κ = 0 := by
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
  have kernel_le : LinearMap.ker a₁Cycles ≤ LinearMap.ker q₁ := by
    intro x hx
    have hx' : x ∈ LinearMap.ker a₁ := congrArg Subtype.val hx
    rw [← exact21] at hx'
    obtain ⟨y, rfl⟩ := hx'
    exact DFunLike.congr_fun zero_component y
  obtain ⟨h, hh⟩ :=
    exists_descend_of_surjective a₁Cycles a₁Cycles_surjective q₁ kernel_le
  let k : LinearMap.ker ε →ₗ[A] c.L := c.π.comp h
  have left_square : c.j.comp k = q₀.comp (LinearMap.ker ε).subtype := by
    ext z
    obtain ⟨x, rfl⟩ := a₁Cycles_surjective z
    change c.γN (h (a₁Cycles x)) = q₀ (a₁ x)
    have hhx : h (a₁Cycles x) = q₁ x := DFunLike.congr_fun hh x
    rw [hhx]
    exact DFunLike.congr_fun square₁ x
  exact splice_zero_of_lifted_comparison c.first_shortExact
    (LinearMap.shortExact_shortComplexKer (f := ε) surjectiveε)
    (ModuleCat.ofHom c.j) (ModuleCat.ofHom c.pQ)
    (ModuleCat.hom_ext c.pQ_j) c.second_shortExact
    (ModuleCat.ofHom k) (ModuleCat.ofHom q₀)
    (ModuleCat.hom_ext left_square) (ModuleCat.hom_ext square₀)
    (ModuleCat.ofHom h) (by rfl)

/-- With a projective cover `Q`, the zero-component comparison gives an actual
linear section of `N → L`, as required after coarse-graining. -/
theorem exists_section_of_zero_component [Module.Projective A Q]
    (c : Syndrome.Cochain A P F Q)
    (a₂ : P₂ →ₗ[A] P₁) (a₁ : P₁ →ₗ[A] P₀) (ε : P₀ →ₗ[A] c.C2)
    (exact21 : LinearMap.range a₂ = LinearMap.ker a₁)
    (exact10 : LinearMap.range a₁ = LinearMap.ker ε)
    (surjectiveε : Function.Surjective ε)
    (q₀ : P₀ →ₗ[A] Q) (q₁ : P₁ →ₗ[A] c.N)
    (square₀ : c.pQ.comp q₀ = ε)
    (square₁ : c.γN.comp q₁ = q₀.comp a₁)
    (zero_component : q₁.comp a₂ = 0) :
    ∃ σ : c.L →ₗ[A] c.N, c.π.comp σ = LinearMap.id :=
  c.κ_zero_iff_section.mp
    (κ_eq_zero_of_zero_component c a₂ a₁ ε exact21 exact10 surjectiveε
      q₀ q₁ square₀ square₁ zero_component)

end Syndrome

end Decoupling.ZeroComparison
