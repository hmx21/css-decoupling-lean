import Decoupling.HighDim.ScalingLattice
import Decoupling.HighDim.ExactIteration

/-!
# Iterated standard scaling is exactly the prescribed physical sublattice

All functor isomorphisms are induced by literal equalities of ring maps.
The final profile comparison is the existing physical trace-duality
comparison, transported only by the chosen integer basis of the final lattice.
-/

namespace Decoupling.HighDim.ScalingLattice

open CategoryTheory CategoryTheory.Limits LatticeRestriction
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

/-- A natural isomorphism of exact module functors induces a natural
isomorphism on their genuine localized derived categories. -/
def derivedFunctorIso {A B : Type} [CommRing A] [CommRing B]
    {F G : ModuleCat A ⥤ ModuleCat B} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (e : F ≅ G) :
    F.mapDerivedCategory ≅ G.mapDerivedCategory :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (ModuleCat A) (.up ℤ))
    (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    F.mapDerivedCategory G.mapDerivedCategory
    (Functor.isoWhiskerRight (NatIso.mapHomologicalComplex e (.up ℤ)) DerivedCategory.Q)

variable (K : Type) [CommRing K] {D : ℕ}

/-- k successive restrictions along scaling by p are precisely restriction
along scaling by p^k, including k = 0. -/
def iteratedScalingIso (p k : ℕ) :
    ExactIteration.iterate (ModuleCat.restrictScalars (Koszul.scaling K D p)) k ≅
      ModuleCat.restrictScalars (Koszul.scaling K D (p ^ k)) := by
  induction k with
  | zero =>
    exact (ModuleCat.restrictScalarsId' _ (by simp)).symm
  | succ k ih =>
    refine Functor.isoWhiskerRight ih _ ≪≫ (ModuleCat.restrictScalarsComp' _ _ _ ?_).symm
    rw [scaling_comp, pow_succ]

/-- The corresponding statement for the iterated exact functor on the
derived category; this transports extension data as well as homology. -/
def iteratedDerivedScalingIso (p k : ℕ) :
    ExactIteration.derived (ModuleCat.restrictScalars (Koszul.scaling K D p)) k ≅
      (ModuleCat.restrictScalars (Koszul.scaling K D (p ^ k))).mapDerivedCategory :=
  ExactIteration.comparison _ k ≪≫ derivedFunctorIso (iteratedScalingIso K p k)

variable (Λ : AddSubgroup (Translation D)) (e : Λ ≃+ Translation D)

/-- A chosen lattice basis only renames the physical profile over its actual
retained subring. -/
def coordinatePhysicalProfile [Λ.FiniteIndex] {q s r : ℕ} (c : CSS.Checks K D q s r) :=
  (ModuleCat.restrictScalars (ringCoordinates K Λ e).symm.toRingHom).mapDerivedCategory.obj
    (LatticeProfile.physicalProfile K Λ c)

def coordinateDerivedRestrictionIso :
    (ModuleCat.restrictScalars (coordinateEmbedding K Λ e)).mapDerivedCategory ≅
      (LatticeExt.restriction K Λ).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars (ringCoordinates K Λ e).symm.toRingHom).mapDerivedCategory :=
  derivedFunctorIso (coordinateRestrictionIso K Λ e) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Exactly the prior physicalProfileIso, followed by the integer-basis
renaming; no extra restriction functor occurs. -/
def coordinatePhysicalProfileIso [Λ.FiniteIndex] {q s r : ℕ}
    (c : CSS.Checks K D q s r) :
    (ModuleCat.restrictScalars (coordinateEmbedding K Λ e)).mapDerivedCategory.obj
        (Profile.S_X c) ≅ coordinatePhysicalProfile K Λ e c :=
  (coordinateDerivedRestrictionIso K Λ e).app _ ≪≫
    (ModuleCat.restrictScalars (ringCoordinates K Λ e).symm.toRingHom).mapDerivedCategory.mapIso
      (LatticeProfile.physicalProfileIso K Λ c)

/-- The derived functor on the actual lattice p^k Lambda is the original
Lambda restriction followed by exactly k applications of standard p-scaling. -/
def iteratedLatticeDerivedIso (p k : ℕ) (hp : p ≠ 0) :
    (ModuleCat.restrictScalars
      (coordinateEmbedding K (LatticeBasis.scaled Λ (p ^ k))
        (scaledCoordinates Λ e (p ^ k) (pow_ne_zero k hp)))).mapDerivedCategory ≅
      (ModuleCat.restrictScalars (coordinateEmbedding K Λ e)).mapDerivedCategory ⋙
        ExactIteration.derived (ModuleCat.restrictScalars (Koszul.scaling K D p)) k :=
  derivedFunctorIso (scaledRestrictionIso K Λ e (p ^ k) (pow_ne_zero k hp)) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
      Functor.isoWhiskerLeft _ (iteratedDerivedScalingIso K p k).symm

/-- The final physical-profile interface: the Postnikov iteration result is
the profile of the actual p^k Lambda matrix restriction in its scaled original basis. -/
def iteratedPhysicalProfileIso [Λ.FiniteIndex] (p k : ℕ) (hp : p ≠ 0)
    {q s r : ℕ} (c : CSS.Checks K D q s r) :
    (ExactIteration.derived (ModuleCat.restrictScalars (Koszul.scaling K D p)) k).obj
      ((ModuleCat.restrictScalars (coordinateEmbedding K Λ e)).mapDerivedCategory.obj
        (Profile.S_X c)) ≅
      (ModuleCat.restrictScalars
        (ringCoordinates K (LatticeBasis.scaled Λ (p ^ k))
          (scaledCoordinates Λ e (p ^ k) (pow_ne_zero k hp))).symm.toRingHom).mapDerivedCategory.obj
        (by
          letI := LatticeBasis.scaled_finiteIndex Λ (pow_ne_zero k hp)
          exact LatticeProfile.physicalProfile K (LatticeBasis.scaled Λ (p ^ k)) c) := by
  letI := LatticeBasis.scaled_finiteIndex Λ (pow_ne_zero k hp)
  exact ((iteratedLatticeDerivedIso K Λ e p k hp).app _).symm ≪≫
    coordinatePhysicalProfileIso K (LatticeBasis.scaled Λ (p ^ k))
      (scaledCoordinates Λ e (p ^ k) (pow_ne_zero k hp)) c

end
end Decoupling.HighDim.ScalingLattice
