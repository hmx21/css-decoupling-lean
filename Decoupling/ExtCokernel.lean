import Decoupling.ExtSplitting
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Computing genuine Ext¹ using a projective cover

For a short exact sequence `0 → K → P → M → 0` with P projective,
Ext¹(M,E) is the cokernel of Hom(P,E) → Hom(K,E). This is a linear equivalence
for genuine derived-category Ext and is an interface for computing the layers
from the conjugated free resolution, without defining Ext as that cokernel.
-/

universe w v u t

namespace Decoupling.ExtCokernel

open CategoryTheory CategoryTheory.Abelian

variable (A : Type t) [CommRing A]
  {C : Type u} [Category.{v} C] [Abelian C] [Linear A C] [HasExt.{w} C]

noncomputable section

/-- Restrict a homomorphism from the projective cover to its kernel. -/
def homRestriction (S : ShortComplex C) (E : C) : (S.X₂ ⟶ E) →ₗ[A] (S.X₁ ⟶ E) where
  toFun f := S.f ≫ f
  map_add' f g := by simp
  map_smul' r f := by simp

/-- The connecting homomorphism, after identifying Ext⁰ with Hom. -/
def connectingHom {S : ShortComplex C} (hS : S.ShortExact) (E : C) :
    (S.X₁ ⟶ E) →ₗ[A] Ext S.X₃ E 1 :=
  (hS.extClass.precompOfLinear A E (add_zero 1)).comp
    (Ext.linearEquiv₀ (R := A)).symm.toLinearMap

@[simp] theorem connectingHom_apply {S : ShortComplex C} (hS : S.ShortExact)
    (E : C) (f : S.X₁ ⟶ E) :
    connectingHom A hS E f = hS.extClass.comp (Ext.mk₀ f) (add_zero 1) := rfl

/-- Exactness of Hom(P,E) → Hom(K,E) → Ext¹(M,E). -/
theorem range_homRestriction {S : ShortComplex C} (hS : S.ShortExact) (E : C) :
    LinearMap.range (homRestriction A S E) = LinearMap.ker (connectingHom A hS E) := by
  ext f
  constructor
  · rintro ⟨g, rfl⟩
    change hS.extClass.comp (Ext.mk₀ (S.f ≫ g)) (add_zero 1) = 0
    rw [← Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc (Ext.mk₀ g)
  · intro hf
    change hS.extClass.comp (Ext.mk₀ f) (add_zero 1) = 0 at hf
    obtain ⟨e, he⟩ := Ext.contravariant_sequence_exact₁ hS E (Ext.mk₀ f) (add_zero 1) hf
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective S.X₂ E).surjective e
    refine ⟨g, (Ext.mk₀_bijective S.X₁ E).injective ?_⟩
    simpa only [Ext.mk₀_comp_mk₀, homRestriction, LinearMap.coe_mk, AddHom.coe_mk] using he

/-- Projectivity of the cover makes the connecting homomorphism surjective. -/
theorem connectingHom_surjective {S : ShortComplex C} (hS : S.ShortExact)
    [Projective S.X₂] (E : C) : Function.Surjective (connectingHom A hS E) := by
  intro e
  obtain ⟨f, hf⟩ := Ext.contravariant_sequence_exact₃ hS E e
    (Ext.eq_zero_of_projective _) (add_zero 1)
  obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective S.X₁ E).surjective f
  exact ⟨g, hf⟩

/-- The actual R-linear cokernel computation for Ext¹. -/
def homCokernelEquivExtOne {S : ShortComplex C} (hS : S.ShortExact)
    [Projective S.X₂] (E : C) :
    ((S.X₁ ⟶ E) ⧸ LinearMap.range (homRestriction A S E)) ≃ₗ[A] Ext S.X₃ E 1 :=
  (Submodule.quotEquivOfEq _ _ (range_homRestriction A hS E)).trans
    ((connectingHom A hS E).quotKerEquivOfSurjective (connectingHom_surjective A hS E))

/-- The degree-one to degree-two dimension shift, now as a linear equivalence. -/
def dimensionShiftEquiv {S : ShortComplex C} (hS : S.ShortExact)
    [Projective S.X₂] (E : C) : Ext S.X₁ E 1 ≃ₗ[A] Ext S.X₃ E 2 :=
  LinearEquiv.ofBijective (hS.extClass.precompOfLinear A E (by decide))
    (ExtSplitting.dimensionShift_bijective hS E)

end
end Decoupling.ExtCokernel
