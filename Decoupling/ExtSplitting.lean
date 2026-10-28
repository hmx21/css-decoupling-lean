import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.Biproducts

/-!
# The genuine Ext obstruction to splitting

These statements use mathlib's derived-category `Ext`, not a replacement
quotient called Ext. They formalize the dimension shift and splitting criterion
used in Proposition III.1 and Appendix B. The two physical short exact sequences
still have to be constructed from the actual CSS input.

Category composition is written left-to-right (`f ≫ g`). Consequently the
Yoneda splice class is `hT.extClass.comp hS.extClass`: first the extension of
B by L, then the extension of L by E. Its zero criterion is independent of the
sign convention for the long-exact connecting homomorphism.
-/

universe w v u

namespace Decoupling.ExtSplitting

open CategoryTheory CategoryTheory.Abelian

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- A short exact sequence has zero genuine Ext¹ class iff its last map has a section. -/
theorem extClass_zero_iff_section {S : ShortComplex C} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ := by
  constructor
  · intro h
    obtain ⟨e, he⟩ := Ext.covariant_sequence_exact₃ S.X₃ hS
      (Ext.mk₀ (𝟙 S.X₃)) (zero_add 1) (by simp [h])
    obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective S.X₃ S.X₂).surjective e
    refine ⟨s, (Ext.mk₀_bijective S.X₃ S.X₃).injective ?_⟩
    simpa only [Ext.mk₀_comp_mk₀] using he
  · rintro ⟨s, hs⟩
    have hzero : (Ext.mk₀ (s ≫ S.g)).comp hS.extClass (zero_add 1) = 0 := by
      rw [← Ext.mk₀_comp_mk₀_assoc, hS.comp_extClass, Ext.comp_zero]
    simpa [hs] using hzero

/-- A zero Ext¹ obstruction produces a full compatible splitting. -/
theorem extClass_zero_iff_splitting {S : ShortComplex C} (hS : S.ShortExact) :
    hS.extClass = 0 ↔ Nonempty S.Splitting := by
  rw [extClass_zero_iff_section hS]
  constructor
  · rintro ⟨s, hs⟩
    exact ⟨ShortComplex.Splitting.ofExactOfSection S hS.exact s hs hS.mono_f⟩
  · rintro ⟨s⟩
    exact ⟨s.s, s.s_g⟩

/-- Dimension shifting through a projective middle object is injective in degree one. -/
theorem dimensionShift_zero_iff {T : ShortComplex C} (hT : T.ShortExact)
    [Projective T.X₂] {E : C} (e : Ext T.X₁ E 1) :
    hT.extClass.comp e (by decide : 1 + 1 = 2) = 0 ↔ e = 0 := by
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Ext.contravariant_sequence_exact₁ hT E e (by decide) h
    rw [Ext.eq_zero_of_projective a, Ext.comp_zero] at ha
    exact ha.symm
  · intro h
    simp [h]

/-- Both adjacent Ext groups of the projective cover vanish, giving the full bijection. -/
theorem dimensionShift_bijective {T : ShortComplex C} (hT : T.ShortExact)
    [Projective T.X₂] (E : C) :
    Function.Bijective (fun e : Ext T.X₁ E 1 =>
      hT.extClass.comp e (by decide : 1 + 1 = 2)) := by
  constructor
  · intro a b h
    have hsub : hT.extClass.comp (a - b) (by decide : 1 + 1 = 2) = 0 := by
      simp [sub_eq_add_neg, h]
    exact sub_eq_zero.mp ((dimensionShift_zero_iff hT (a - b)).mp hsub)
  · intro e
    exact Ext.contravariant_sequence_exact₃ hT E e (Ext.eq_zero_of_projective _) (by decide)

/-- The splice vanishes exactly when the first sequence splits (Proposition III.1).
The middle term Q of the second short exact sequence is projective, as for R^{c_X}. -/
theorem splice_zero_iff_splitting {S : ShortComplex C} (hS : S.ShortExact)
    {Q B : C} [Projective Q] (j : S.X₃ ⟶ Q) (p : Q ⟶ B) (hjp : j ≫ p = 0)
    (hT : (ShortComplex.mk j p hjp).ShortExact) :
    hT.extClass.comp hS.extClass (by decide : 1 + 1 = 2) = 0 ↔
      Nonempty S.Splitting :=
  (dimensionShift_zero_iff hT hS.extClass).trans (extClass_zero_iff_splitting hS)

/-- For actual R-modules a vanishing Ext¹ class gives the direct-product linear equivalence.
Finite direct products here are the manuscript's finite direct sums. -/
noncomputable def moduleEquivProd {A : Type u} [Ring A]
    {S : ShortComplex (ModuleCat.{u} A)} (hS : S.ShortExact) (h : hS.extClass = 0) :
    S.X₂ ≃ₗ[A] (S.X₁ × S.X₃) := by
  let s := Classical.choice ((extClass_zero_iff_splitting hS).mp h)
  exact (s.isoBinaryBiproduct ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv

end Decoupling.ExtSplitting
