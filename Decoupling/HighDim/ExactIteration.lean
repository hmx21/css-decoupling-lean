import Decoupling.HighDim.ExactDerivedHomology
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # Iterated exact restriction and its actual derived functor -/

namespace Decoupling.HighDim.ExactIteration

open CategoryTheory CategoryTheory.Limits
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category* C]

def iterate (F : C ⥤ C) : ℕ → C ⥤ C
  | 0 => 𝟭 C
  | n + 1 => iterate F n ⋙ F

@[simp] theorem iterate_zero_obj (F : C ⥤ C) (X : C) : (iterate F 0).obj X = X := rfl
@[simp] theorem iterate_succ_obj (F : C ⥤ C) (n : ℕ) (X : C) :
    (iterate F (n + 1)).obj X = F.obj ((iterate F n).obj X) := rfl

instance iterate_additive [Preadditive C] (F : C ⥤ C) [F.Additive] (n : ℕ) :
    (iterate F n).Additive := by
  induction n with
  | zero => exact inferInstanceAs (𝟭 C).Additive
  | succ n ih => exact inferInstanceAs (iterate F n ⋙ F).Additive

instance iterate_preservesFiniteLimits (F : C ⥤ C) [PreservesFiniteLimits F] (n : ℕ) :
    PreservesFiniteLimits (iterate F n) := by
  induction n with
  | zero => exact inferInstanceAs (PreservesFiniteLimits (𝟭 C))
  | succ n ih => exact inferInstanceAs (PreservesFiniteLimits (iterate F n ⋙ F))

instance iterate_preservesFiniteColimits (F : C ⥤ C) [PreservesFiniteColimits F] (n : ℕ) :
    PreservesFiniteColimits (iterate F n) := by
  induction n with
  | zero => exact inferInstanceAs (PreservesFiniteColimits (𝟭 C))
  | succ n ih => exact inferInstanceAs (PreservesFiniteColimits (iterate F n ⋙ F))

instance iterate_commShift [HasShift C ℤ] (F : C ⥤ C) [F.CommShift ℤ] (n : ℕ) :
    (iterate F n).CommShift ℤ := by
  induction n with
  | zero => exact inferInstanceAs ((𝟭 C).CommShift ℤ)
  | succ n ih => exact inferInstanceAs ((iterate F n ⋙ F).CommShift ℤ)

instance iterate_triangulated [HasZeroObject C] [Preadditive C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (F : C ⥤ C) [F.CommShift ℤ] [F.IsTriangulated] (n : ℕ) :
    (iterate F n).IsTriangulated := by
  induction n with
  | zero => exact inferInstanceAs (𝟭 C).IsTriangulated
  | succ n ih => exact inferInstanceAs (iterate F n ⋙ F).IsTriangulated

variable [Abelian C] (F : C ⥤ C) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

abbrev derived (n : ℕ) := iterate F.mapDerivedCategory n

def singleIso (n : ℕ) (j : ℤ) (M : C) :
    (derived F n).obj ((DerivedCategory.singleFunctor C j).obj M) ≅
      (DerivedCategory.singleFunctor C j).obj ((iterate F n).obj M) := by
  induction n with
  | zero => exact Iso.refl _
  | succ n ih => exact F.mapDerivedCategory.mapIso ih ≪≫
      (F.mapDerivedCategorySingleFunctor j).app ((iterate F n).obj M)

def comparison (n : ℕ) : derived F n ≅ (iterate F n).mapDerivedCategory := by
  induction n with
  | zero => exact (Functor.mapDerivedCategoryIdIso (C₁ := C)).symm
  | succ n ih => exact Functor.isoWhiskerRight ih F.mapDerivedCategory ≪≫
      Functor.mapDerivedCategoryCompIso (iterate F n) F

end
end Decoupling.HighDim.ExactIteration
