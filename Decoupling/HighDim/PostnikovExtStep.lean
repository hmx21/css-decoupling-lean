import Decoupling.HighDim.PostnikovStep
import Decoupling.HighDim.ShiftedExt

/-!
# Native positive Ext vanishing splits a single Postnikov extension

The lower biproduct is a previously constructed derived isomorphism.
Only then are its connecting components identified with native Ext.
-/

namespace Decoupling.HighDim.PostnikovExtStep

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated CategoryTheory.Abelian
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category* C] [Abelian C] [HasExt C]
  {D : Type*} [Category* D] [Abelian D] [HasExt D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

theorem splits_of_native_ext (T : Triangle (DerivedCategory C)) (hT : T ∈ distTriang _)
    {ι : Type} [Fintype ι] (degree : ι → ℤ) (B : ι → C) (j : ℤ) (A : C)
    (hdeg : ∀ i, degree i < j)
    (eLower : T.obj₁ ≅ ⨁ (fun i => (DerivedCategory.singleFunctor C (degree i)).obj (B i)))
    (eUpper : T.obj₃ ≅ (DerivedCategory.singleFunctor C j).obj A)
    (hExt : ∀ i (n : ℕ), 0 < n → ∀ e : Ext A (B i) n, e.mapExactFunctor F = 0) :
    ∃ e : F.mapDerivedCategory.obj T.obj₁ ⊞ F.mapDerivedCategory.obj T.obj₃ ≅
        F.mapDerivedCategory.obj T.obj₂,
      biprod.inl ≫ e.hom = F.mapDerivedCategory.map T.mor₁ ∧
        e.hom ≫ F.mapDerivedCategory.map T.mor₂ = biprod.snd := by
  apply PostnikovStep.mapped_triangle_splits_of_lower_biproduct F.mapDerivedCategory T hT
    (fun i => (DerivedCategory.singleFunctor C (degree i)).obj (B i)) eLower
  intro i
  let n : ℕ := (j - degree i + 1).toNat
  have hn : (n : ℤ) = j - degree i + 1 := Int.toNat_of_nonneg (by have := hdeg i; omega)
  have hnpos : 0 < n := by have := hdeg i; omega
  have hh := ShiftedExt.map_connecting_component_eq_zero F (degree i) j n hn
    (hExt i n hnpos)
    (eUpper.inv ≫ T.mor₃ ≫ eLower.hom⟦(1 : ℤ)⟧' ≫
      (biproduct.π (fun i => (DerivedCategory.singleFunctor C (degree i)).obj (B i)) i)⟦(1 : ℤ)⟧')
  exact (cancel_epi (F.mapDerivedCategory.map eUpper.inv)).mp
    (by simpa only [Functor.map_comp, Category.assoc, comp_zero] using hh)

end
end Decoupling.HighDim.PostnikovExtStep
