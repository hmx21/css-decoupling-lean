import Decoupling.YonedaCocycle
import Decoupling.CoarseVanishing
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! Genuine Ext² represented by the actual two syzygies of an exact prefix. -/

namespace Decoupling.GeneralExtRestriction

open CategoryTheory CategoryTheory.Abelian

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (A : Type) [CommRing A]
variable (P₀ P₁ B : Type) [AddCommGroup P₀] [Module A P₀]
  [AddCommGroup P₁] [Module A P₁] [AddCommGroup B] [Module A B]

/-- Two terms of a genuinely exact augmented presentation. -/
structure Prefix where
  ε : P₀ →ₗ[A] B
  a₁ : P₁ →ₗ[A] P₀
  exact : LinearMap.range a₁ = LinearMap.ker ε
  surjective : Function.Surjective ε

namespace Prefix

variable {A P₀ P₁ B} (p : Prefix A P₀ P₁ B)

abbrev K₁ := LinearMap.ker p.ε

def cover : P₁ →ₗ[A] p.K₁ := p.a₁.codRestrict _ (by
  intro x
  change p.a₁ x ∈ LinearMap.ker p.ε
  rw [← p.exact]
  exact ⟨x, rfl⟩)

theorem cover_surjective : Function.Surjective p.cover := by
  intro x
  have hx : (x : P₀) ∈ LinearMap.range p.a₁ := by rw [p.exact]; exact x.property
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

abbrev K₂ := LinearMap.ker p.cover
abbrev U := p.ε.shortComplexKer
abbrev V := p.cover.shortComplexKer

theorem shortExactU : p.U.ShortExact := LinearMap.shortExact_shortComplexKer p.surjective
theorem shortExactV : p.V.ShortExact := LinearMap.shortExact_shortComplexKer p.cover_surjective

def cocycleClass (E : ModuleCat A) (f : ModuleCat.of A p.K₂ ⟶ E) :
    Ext (ModuleCat.of A B) E 2 :=
  YonedaCocycle.cocycleClass p.shortExactU p.shortExactV f

/-- Every genuine Ext² element has a representative on the second syzygy,
provided the two covers are actually projective. -/
theorem exists_representative [Module.Projective A P₀] [Module.Projective A P₁]
    (E : ModuleCat A) (e : Ext (ModuleCat.of A B) E 2) :
    ∃ f : ModuleCat.of A p.K₂ ⟶ E, p.cocycleClass E f = e := by
  let eclass := YonedaCocycle.cocycleQuotientEquiv p.shortExactU p.shortExactV A E
  obtain ⟨f, hf⟩ :=
    (LinearMap.range (ExtCokernel.homRestriction A p.V E)).mkQ_surjective (eclass.symm e)
  refine ⟨f, ?_⟩
  rw [cocycleClass, ← YonedaCocycle.cocycleQuotientEquiv_mk
    p.shortExactU p.shortExactV A f]
  change eclass (Submodule.Quotient.mk f) = e
  exact (congrArg eclass hf).trans (eclass.apply_symm_apply e)

/-- Restriction here is the genuine exact-functor map on derived Ext. -/
theorem map_cocycleClass {A' : Type} [CommRing A']
    (F : ModuleCat A ⥤ ModuleCat A') [F.Additive]
    [Limits.PreservesFiniteLimits F] [Limits.PreservesFiniteColimits F]
    (E : ModuleCat A) (f : ModuleCat.of A p.K₂ ⟶ E) :
    (p.cocycleClass E f).mapExactFunctor F =
      YonedaCocycle.cocycleClass (p.shortExactU.map_of_exact F)
        (p.shortExactV.map_of_exact F) (F.map f) := by
  simp only [cocycleClass, YonedaCocycle.cocycleClass, Ext.mapExactFunctor_comp,
    Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_mk₀]

end Prefix

/-- The literal doubled subring preserves arbitrary projective modules,
not only free ones: restrict a genuine splitting of a free cover. -/
theorem projective_restrict (M : Type*) [AddCommGroup M]
    [Module R M] [Module RetainedRing.S M] [IsScalarTower RetainedRing.S R M]
    [Module.Projective R M] : Module.Projective RetainedRing.S M := by
  obtain ⟨i, hi⟩ := (Module.projective_def' (R := R) (P := M)).mp inferInstance
  let : Module.Projective RetainedRing.S (M →₀ R) :=
    CoarseBasis.projective_restrict_of_free (M →₀ R)
  apply Module.Projective.of_split (i.restrictScalars RetainedRing.S)
    ((Finsupp.linearCombination R id).restrictScalars RetainedRing.S)
  apply LinearMap.ext
  intro m
  exact DFunLike.congr_fun hi m

end
end Decoupling.GeneralExtRestriction
