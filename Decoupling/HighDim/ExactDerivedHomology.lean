import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Homology of the derived functor of an exact functor

The isomorphism is induced from a genuine representative complex and the
actual homology comparison, so it does not assume derived formality.
-/

namespace Decoupling.HighDim.ExactDerivedHomology

open CategoryTheory CategoryTheory.Limits
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {C : Type*} [Category* C] [Abelian C]
  {D : Type*} [Category* D] [Abelian D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

def complexHomologyIso (K : CochainComplex C ℤ) (i : ℤ) :
    ((F.mapHomologicalComplex (.up ℤ)).obj K).homology i ≅ F.obj (K.homology i) :=
  (K.sc i).mapHomologyIso F

def homologyIso (X : DerivedCategory C) (i : ℤ) :
    (DerivedCategory.homologyFunctor D i).obj (F.mapDerivedCategory.obj X) ≅
      F.obj ((DerivedCategory.homologyFunctor C i).obj X) := by
  let K : CochainComplex C ℤ := DerivedCategory.Q.objPreimage X
  let e : DerivedCategory.Q.obj K ≅ X := DerivedCategory.Q.objObjPreimageIso X
  exact (DerivedCategory.homologyFunctor D i).mapIso
      (F.mapDerivedCategory.mapIso e.symm ≪≫ F.mapDerivedCategoryFactors.app K) ≪≫
    (DerivedCategory.homologyFunctorFactors D i).app _ ≪≫
    complexHomologyIso F K i ≪≫
    F.mapIso ((DerivedCategory.homologyFunctorFactors C i).symm.app K ≪≫
      (DerivedCategory.homologyFunctor C i).mapIso e)

theorem isGE (X : DerivedCategory C) (n : ℤ) [X.IsGE n] :
    (F.mapDerivedCategory.obj X).IsGE n := by
  apply (DerivedCategory.isGE_iff _ _).mpr
  intro i hi
  exact (F.map_isZero (DerivedCategory.isZero_of_isGE X n i hi)).of_iso (homologyIso F X i)

theorem isLE (X : DerivedCategory C) (n : ℤ) [X.IsLE n] :
    (F.mapDerivedCategory.obj X).IsLE n := by
  apply (DerivedCategory.isLE_iff _ _).mpr
  intro i hi
  exact (F.map_isZero (DerivedCategory.isZero_of_isLE X n i hi)).of_iso (homologyIso F X i)

end
end Decoupling.HighDim.ExactDerivedHomology
