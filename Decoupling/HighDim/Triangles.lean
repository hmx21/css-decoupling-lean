import Mathlib.CategoryTheory.Triangulated.Pretriangulated

/-!
# The distinguished-triangle splitting criterion (Lemma 4)

Source: `drafts/appendix.tex` 127–165. This uses mathlib's actual
pretriangulated-category results and preserves the inclusion and projection.
It does not replace the derived profile by its cohomology or assume that a
specific truncation triangle splits. The later profile construction must
supply its actual distinguished truncation triangles.
-/

namespace Decoupling.HighDim.Triangles

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, Functor.Additive (shiftFunctor C n)] [Pretriangulated C]

theorem connecting_eq_zero_iff_section (T : Triangle C) (hT : T ∈ distTriang C) :
    T.mor₃ = 0 ↔ ∃ σ : T.obj₃ ⟶ T.obj₂, σ ≫ T.mor₂ = 𝟙 T.obj₃ := by
  constructor
  · intro h
    obtain ⟨σ, hσ⟩ := T.coyoneda_exact₃ hT (𝟙 T.obj₃) (by simp [h])
    exact ⟨σ, hσ.symm⟩
  · rintro ⟨σ, hσ⟩
    calc
      T.mor₃ = (σ ≫ T.mor₂) ≫ T.mor₃ := by rw [hσ, Category.id_comp]
      _ = 0 := by rw [Category.assoc, comp_distTriang_mor_zero₂₃ T hT, comp_zero]

theorem connecting_eq_zero_iff_compatible_biproduct
    (T : Triangle C) (hT : T ∈ distTriang C) :
    T.mor₃ = 0 ↔ ∃ e : T.obj₁ ⊞ T.obj₃ ≅ T.obj₂,
      biprod.inl ≫ e.hom = T.mor₁ ∧ e.hom ≫ T.mor₂ = biprod.snd := by
  constructor
  · intro h
    obtain ⟨e, hi, hp⟩ := exists_iso_binaryBiproduct_of_distTriang T hT h
    refine ⟨e.symm, ?_, ?_⟩
    · rw [← hi]
      simp
    · rw [hp]
      simp
  · rintro ⟨e, _, hp⟩
    apply (connecting_eq_zero_iff_section T hT).mpr
    refine ⟨biprod.inr ≫ e.hom, ?_⟩
    rw [Category.assoc, hp, biprod.inr_snd]

end Decoupling.HighDim.Triangles
