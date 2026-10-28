import Decoupling.HighDim.ScalingLatticeChecksProfile
import Decoupling.HighDim.Lambda0Profile
import Decoupling.HighDim.KoszulLatticeRestriction

/-!
# Restriction through an arbitrary nested pair of integer lattices

The actual subgroup inclusion, expressed in independently chosen bases,
composes to the original inclusion. This gives a natural isomorphism of
exact restriction functors and their genuine derived functors, retaining
all native gluing data. No rectangular lattice or compatible basis is assumed.
-/

namespace Decoupling.HighDim.TwoLayer

open CategoryTheory CategoryTheory.Limits ScalingLattice
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {D : ℕ} (Λ Γ : AddSubgroup (Translation D)) (h : Γ ≤ Λ)
  (eΛ : Λ ≃+ Translation D) (eΓ : Γ ≃+ Translation D)

def nestedCoordinateMap : Translation D →+ Translation D :=
  eΛ.toAddMonoidHom.comp ((AddSubgroup.inclusion h).comp eΓ.symm.toAddMonoidHom)

@[simp] theorem nestedCoordinateMap_apply (a : Translation D) :
    nestedCoordinateMap Λ Γ h eΛ eΓ a = eΛ ⟨(eΓ.symm a : Translation D), h (eΓ.symm a).property⟩ := rfl

theorem nestedCoordinateMap_injective : Function.Injective (nestedCoordinateMap Λ Γ h eΛ eΓ) :=
  eΛ.injective.comp ((AddSubgroup.inclusion_injective h).comp eΓ.symm.injective)

variable (K : Type) [CommRing K]

theorem coordinateEmbedding_nested :
    coordinateEmbedding K Γ eΓ = (coordinateEmbedding K Λ eΛ).comp
      (KoszulLattice.latticeMap K (nestedCoordinateMap Λ Γ h eΛ eΓ)) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro c
    change coordinateEmbedding K Γ eΓ (constant c) = coordinateEmbedding K Λ eΛ
      (KoszulLattice.latticeMap K (nestedCoordinateMap Λ Γ h eΛ eΓ) (constant c))
    simp [KoszulLattice.latticeMap, constant]
  · intro a
    change coordinateEmbedding K Γ eΓ (monomial K a) = coordinateEmbedding K Λ eΛ
      (KoszulLattice.latticeMap K (nestedCoordinateMap Λ Γ h eΛ eΓ) (monomial K a))
    simp [KoszulLattice.latticeMap, monomial]

def nestedRestrictionIso : ModuleCat.restrictScalars (coordinateEmbedding K Γ eΓ) ≅
    ModuleCat.restrictScalars (coordinateEmbedding K Λ eΛ) ⋙
      ModuleCat.restrictScalars (KoszulLattice.latticeMap K (nestedCoordinateMap Λ Γ h eΛ eΓ)) :=
  ModuleCat.restrictScalarsComp' _ _ _ (coordinateEmbedding_nested Λ Γ h eΛ eΓ K)

def nestedDerivedRestrictionIso :
    (ModuleCat.restrictScalars (coordinateEmbedding K Γ eΓ)).mapDerivedCategory ≅
      (ModuleCat.restrictScalars (coordinateEmbedding K Λ eΛ)).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars
          (KoszulLattice.latticeMap K (nestedCoordinateMap Λ Γ h eΛ eΓ))).mapDerivedCategory :=
  derivedFunctorIso (nestedRestrictionIso Λ Γ h eΛ eΓ K) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- A natural comparison on every genuine derived object, not merely on its homology. -/
def nestedProfileIso (X : DerivedCategory (ModuleCat (Laurent K D))) :
    (ModuleCat.restrictScalars
      (KoszulLattice.latticeMap K (nestedCoordinateMap Λ Γ h eΛ eΓ))).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars (coordinateEmbedding K Λ eΛ)).mapDerivedCategory.obj X) ≅
      (ModuleCat.restrictScalars (coordinateEmbedding K Γ eΓ)).mapDerivedCategory.obj X :=
  ((nestedDerivedRestrictionIso Λ Γ h eΛ eΓ K).app X).symm

variable [Γ.FiniteIndex] {q s r : ℕ}

def nestedPhysicalProfileIso (c : CSS.Checks K D q s r) :
    (ModuleCat.restrictScalars
      (KoszulLattice.latticeMap K (nestedCoordinateMap Λ Γ h eΛ eΓ))).mapDerivedCategory.obj
        ((ModuleCat.restrictScalars (coordinateEmbedding K Λ eΛ)).mapDerivedCategory.obj
          (Profile.S_X c)) ≅ Profile.S_X (physicalChecks K Γ eΓ c) :=
  nestedProfileIso Λ Γ h eΛ eΓ K (Profile.S_X c) ≪≫
    physicalChecksRestrictionIso K Γ eΓ c

end
end Decoupling.HighDim.TwoLayer
