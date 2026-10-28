import Decoupling.HighDim.TorusTensorMapsFinite
import Decoupling.HighDim.PerfectModelBasic
import Mathlib.Algebra.Homology.HomotopyCategory.ShiftSequence

/-!
# Actual shift identifications for tensor homology

In particular H⁰ of the shifted lower model is genuinely H¹ of its
unshifted scalar extension, with the canonical cochain shift signs.
-/
namespace Decoupling.HighDim.Torus
open CategoryTheory HomologicalComplex
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {D : ℕ}

instance augmentationExtension_additive :
    (ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).Additive where
  map_add := by
    intro M N f g
    apply ModuleCat.ExtendScalars.hom_ext
    intro v
    simp [ModuleCat.ExtendScalars.map_tmul, TensorProduct.tmul_add]

abbrev tensorHi (C : CochainComplex (ModuleCat (Laurent K D)) ℤ) (i : ℤ) : ModuleCat K :=
  Layers.coefficients ((tensorRestrictedComplex C).homology i)

def tensorShiftHomologyIso (C : CochainComplex (ModuleCat (Laurent K D)) ℤ)
    (a i j : ℤ) (h : a + i = j) : tensorHi (C⟦a⟧) i ≅ tensorHi C j :=
  (ModuleCat.restrictScalars (constant : K →+* Laurent K D)).mapIso
    (((HomologicalComplex.homologyFunctor (ModuleCat (Laurent K D)) (.up ℤ) i).mapIso
      ((((extensionRestricted (augmentation : Laurent K D →+* K)).mapHomologicalComplex
        (.up ℤ)).commShiftIso a).app C)) ≪≫
      (((HomologicalComplex.homologyFunctor (ModuleCat (Laurent K D)) (.up ℤ) 0).shiftIso
        a i j h).app (tensorRestrictedComplex C)))

def TensorModel.shiftH0Iso {X : Derived.{0} K D} (M : TensorModel X) (a : ℤ) :
    (PerfectModel.shift M a).H0 ≅ tensorHi M.complex a :=
  tensorShiftHomologyIso M.complex a 0 a (add_zero a)

/-- Postcomposition by the canonical H⁰-shift/H¹ identification preserves
exactly the image dimension. -/
theorem finrank_range_postcompose_iso {U V W : ModuleCat K} [Module.Finite K U]
    (f : U ⟶ V) (e : V ≅ W) :
    Module.finrank K (f ≫ e.hom).hom.range = Module.finrank K f.hom.range := by
  have hk : (f ≫ e.hom).hom.ker = f.hom.ker := by
    ext x
    change e.hom (f x) = 0 ↔ f x = 0
    exact e.toLinearEquiv.map_eq_zero_iff
  have h₁ := f.hom.finrank_range_add_finrank_ker
  have h₂ := (f ≫ e.hom).hom.finrank_range_add_finrank_ker
  rw [hk] at h₂
  omega

end
end Decoupling.HighDim.Torus
