import Decoupling.HighDim.Triangles
import Mathlib.CategoryTheory.Triangulated.Functor
import Mathlib.CategoryTheory.Preadditive.Biproducts

/-!
# The splitting step after a lower truncation has already split

This is the categorical part of Lemma 2. A connecting morphism into the
shift of an actual finite biproduct has one component per summand. If an
additive triangulated functor kills those components, the image of the
actual distinguished triangle splits. The Ext restriction theorem and
the construction of the canonical truncation tower are separate inputs
to the later induction; this module does not assume a full splitting.
-/

namespace Decoupling.HighDim.PostnikovStep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open CategoryTheory.Pretriangulated
noncomputable section

universe u v u' v'
variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]
  [HasShift C ℤ] [∀ k : ℤ, Functor.Additive (shiftFunctor C k)] [Pretriangulated C]
  {D : Type u'} [Category.{v'} D] [Preadditive D] [HasZeroObject D]
  [HasShift D ℤ] [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D]
  (F : C ⥤ D) [F.Additive]

omit [HasZeroObject C] [Pretriangulated C] [HasZeroObject D]
  [HasShift D ℤ] [∀ k : ℤ, Functor.Additive (shiftFunctor D k)] [Pretriangulated D] in
/-- Killing every component into a shifted finite biproduct kills the whole map. -/
theorem map_eq_zero_of_components {ι : Type} [Fintype ι] (B : ι → C) [HasBiproduct B]
    {A : C} (k : ℤ) (f : A ⟶ (⨁ B)⟦k⟧)
    (h : ∀ i, F.map (f ≫ (biproduct.π B i)⟦k⟧') = 0) : F.map f = 0 := by
  calc
    F.map f = F.map (f ≫ (shiftFunctor C k).map
        (∑ i, biproduct.π B i ≫ biproduct.ι B i)) := by simp
    _ = ∑ i, F.map (f ≫ (biproduct.π B i)⟦k⟧') ≫ F.map ((biproduct.ι B i)⟦k⟧') := by
      simp only [Functor.map_sum, Functor.map_comp, comp_sum, Category.assoc]
    _ = 0 := by simp only [h, zero_comp, Finset.sum_const_zero]

variable [F.CommShift ℤ] [F.IsTriangulated]

omit [F.Additive] in
theorem mapped_triangle_splits (T : Triangle C) (hT : T ∈ distTriang C)
    (h : F.map T.mor₃ = 0) :
    ∃ e : F.obj T.obj₁ ⊞ F.obj T.obj₃ ≅ F.obj T.obj₂,
      biprod.inl ≫ e.hom = F.map T.mor₁ ∧ e.hom ≫ F.map T.mor₂ = biprod.snd := by
  apply (Triangles.connecting_eq_zero_iff_compatible_biproduct
    (F.mapTriangle.obj T) (F.map_distinguished T hT)).mp
  change F.map T.mor₃ ≫ _ = 0
  rw [h, zero_comp]

/-- This applies only after an isomorphism of the lower object with the
displayed biproduct has been constructed. The component condition is then
precisely the condition supplied by the positive-Ext restriction lemma. -/
theorem mapped_triangle_splits_of_lower_biproduct
    (T : Triangle C) (hT : T ∈ distTriang C)
    {ι : Type} [Fintype ι] (B : ι → C) [HasBiproduct B]
    (e : T.obj₁ ≅ ⨁ B)
    (h : ∀ i, F.map (T.mor₃ ≫ e.hom⟦(1 : ℤ)⟧' ≫ (biproduct.π B i)⟦(1 : ℤ)⟧') = 0) :
    ∃ e' : F.obj T.obj₁ ⊞ F.obj T.obj₃ ≅ F.obj T.obj₂,
      biprod.inl ≫ e'.hom = F.map T.mor₁ ∧ e'.hom ≫ F.map T.mor₂ = biprod.snd := by
  apply mapped_triangle_splits F T hT
  have hf := map_eq_zero_of_components F B 1 (T.mor₃ ≫ e.hom⟦(1 : ℤ)⟧')
    (by intro i; simpa only [Category.assoc] using h i)
  apply (cancel_mono (F.map (e.hom⟦(1 : ℤ)⟧'))).mp
  simpa only [Functor.map_comp, zero_comp] using hf

end
end Decoupling.HighDim.PostnikovStep
