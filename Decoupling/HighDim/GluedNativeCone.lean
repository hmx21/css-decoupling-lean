import Decoupling.HighDim.GluedNativeClass
import Decoupling.HighDim.TwoLayerPostnikov
import Mathlib.Algebra.Homology.Embedding.HomEquiv

/-!
# The actual cone of the displayed augmentation cocycle

The source is the proved Koszul resolution placed in degree 3. Taking
the cone of its -12 augmentation to the coefficient module in degree 1
produces the two-layer extension. The comparison with the displayed
check matrices is developed subsequently.
-/

namespace Decoupling.HighDim.Glued

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex CochainComplex.HomComplex Koszul
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

/-- The actual map `K[degree 3] → F[degree 1]` induced by the displayed
coupling. Its cocycle equation is proved from the real Koszul differential. -/
def couplingToSingle : Toric.model K 3 3 ⟶
    (CochainComplex.singleFunctor (ModuleCat (Laurent K 3)) 1).obj (coefficientModule K 3) :=
  mkHomToSingle ((Toric.termIso K 3 3 2).hom ≫ couplingCochain K) (by
    intro i hi
    change i + 1 = 1 at hi
    have hi0 : i = 0 := by omega
    subst i
    rw [show (Toric.model K 3 3).d 0 1 =
      (Toric.termIso K 3 3 3).hom ≫ boundary (Laurent K 3) (difference K) 2 ≫
        (Toric.termIso K 3 3 2).inv from Toric.differential K 3 3 2]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, couplingCochain_boundary, comp_zero])

/-- The native mapping cone, rather than a surrogate two-layer object. -/
def couplingCone : CochainComplex (ModuleCat (Laurent K 3)) ℤ :=
  CochainComplex.mappingCone (couplingToSingle K)

/-- The distinguished triangle retaining the native connecting class. -/
def couplingTriangle : Triangle (DerivedCategory (ModuleCat (Laurent K 3))) :=
  (DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle (couplingToSingle K))).rotate

theorem couplingTriangle_distinguished : couplingTriangle K ∈ distTriang _ := by
  apply rot_of_distTriang
  exact DerivedCategory.mappingCone_triangle_distinguished (couplingToSingle K)

/-- The left endpoint of the actual extension is the coefficient module
in degree 1. -/
def couplingTriangleLeftIso : (couplingTriangle K).obj₁ ≅
    (DerivedCategory.singleFunctor (ModuleCat (Laurent K 3)) 1).obj (coefficientModule K 3) :=
  Iso.refl _

/-- The right endpoint is the coefficient module in degree 2, using the
proved augmentation of the degree-3 Koszul model and the native shift. -/
def couplingTriangleRightIso : (couplingTriangle K).obj₃ ≅
    (DerivedCategory.singleFunctor (ModuleCat (Laurent K 3)) 2).obj (coefficientModule K 3) :=
  (shiftFunctor (DerivedCategory (ModuleCat (Laurent K 3))) (1 : ℤ)).mapIso
    (Toric.derivedIso K 3 3) ≪≫
      ((DerivedCategory.singleFunctors (ModuleCat (Laurent K 3))).shiftIso
        1 2 3 (by norm_num)).app (coefficientModule K 3)

/-- The cochain-level cone is the middle object of this actual distinguished
extension triangle. -/
def couplingTriangleMiddleIso : (couplingTriangle K).obj₂ ≅ DerivedCategory.Q.obj (couplingCone K) :=
  Iso.refl _

end
end Decoupling.HighDim.Glued
