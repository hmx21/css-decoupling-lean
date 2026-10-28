import Decoupling.HighDim.TorusTensorMapsCoherence

/-!
# The actual tensor-induced map on individual homology classes

This is the chain-to-homology endpoint used for explicit Koszul
contraction formulas. The formula is proved for arbitrary chain maps.
-/
namespace Decoupling.HighDim.Torus
open CategoryTheory HomologicalComplex
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] {D : ℕ}

abbrev tensorRestrictedComplex (C : CochainComplex (ModuleCat (Laurent K D)) ℤ) :=
  ((extensionRestricted (augmentation : Laurent K D →+* K)).mapHomologicalComplex (.up ℤ)).obj C

def tensorCycleClass (C : CochainComplex (ModuleCat (Laurent K D)) ℤ)
    (x : (tensorRestrictedComplex C).X 0)
    (hx : (tensorRestrictedComplex C).d 0 ((ComplexShape.up ℤ).next 0) x = 0) : tensorH0 C :=
  Glued.cycleClass ((tensorRestrictedComplex C).sc 0) x hx

theorem tensorH0Map_cycleClass {C E : CochainComplex (ModuleCat (Laurent K D)) ℤ}
    (f : C ⟶ E) (x : (tensorRestrictedComplex C).X 0)
    (hx : (tensorRestrictedComplex C).d 0 ((ComplexShape.up ℤ).next 0) x = 0) :
    tensorH0Map f (tensorCycleClass C x hx) =
      tensorCycleClass E ((extensionRestricted augmentation).map (f.f 0) x) (by
        have h := (((extensionRestricted augmentation).mapHomologicalComplex (.up ℤ)).map f).comm
          0 ((ComplexShape.up ℤ).next 0)
        change (extensionRestricted augmentation).map (f.f 0) ≫
          (tensorRestrictedComplex E).d 0 ((ComplexShape.up ℤ).next 0) = _ at h
        change (_ ≫ (tensorRestrictedComplex E).d 0 ((ComplexShape.up ℤ).next 0)) x = 0
        rw [h]
        change ((extensionRestricted augmentation).map (f.f ((ComplexShape.up ℤ).next 0)))
          ((tensorRestrictedComplex C).d 0 ((ComplexShape.up ℤ).next 0) x) = 0
        rw [hx, map_zero]) :=
  Glued.homologyMap_cycleClass
    ((shortComplexFunctor (ModuleCat (Laurent K D)) (.up ℤ) 0).map
      (((extensionRestricted augmentation).mapHomologicalComplex (.up ℤ)).map f)) x hx

end
end Decoupling.HighDim.Torus
