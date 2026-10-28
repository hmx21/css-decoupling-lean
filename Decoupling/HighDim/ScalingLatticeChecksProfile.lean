import Decoupling.HighDim.ScalingLatticeChecks

/-!
# The native profile of the actual renamed finite check matrices

The final isomorphism identifies iterated standard scaling with the genuine
S_X of the literal p^k Lambda physical checks. It retains all extension
data, and the only coordinate changes are the fixed coset basis and the
scaled original integer-lattice basis.
-/

namespace Decoupling.HighDim.ScalingLattice

open CategoryTheory CategoryTheory.Abelian LatticeRestriction LatticeExt
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [CommRing K] {D : ℕ}
  (Λ : AddSubgroup (Translation D)) (e : Λ ≃+ Translation D)

/-- Laurent conjugation commutes with an arbitrary integer-lattice basis. -/
def conjugationRenameIso (M : ModuleCat (S K Λ)) :
    (RingChange.rename (ringCoordinates K Λ e)).obj (conjugateS K Λ M) ≅
      Layers.conjugate ((RingChange.rename (ringCoordinates K Λ e)).obj M) :=
  LatticeExt.moduleIso {
    toFun m := m
    invFun m := m
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' a m := by
      change barS K Λ ((ringCoordinates K Λ e).symm a) • (show M from m) =
        (ringCoordinates K Λ e).symm (bar a) • (show M from m)
      congr 1
      apply (ringCoordinates K Λ e).injective
      rw [ringCoordinates_bar, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply] }

variable [Λ.FiniteIndex]

def conjugateReducedRenameIso {q s r : ℕ} (c : CSS.Checks K D q s r) :
    (RingChange.rename (ringCoordinates K Λ e)).obj
      (conjugateS K Λ (LatticeCompatibility.reduced K Λ c)) ≅
        Layers.conjugate (Layers.reduced (physicalChecks K Λ e c)) :=
  conjugationRenameIso K Λ e _ ≪≫
    Layers.conjugationEquivalence.functor.mapIso (reducedRenameIso K Λ e c)

/-- Full native derived-profile compatibility with the actual finite
coset-expanded and integer-basis-renamed check matrices. -/
def physicalChecksProfileIso {q s r : ℕ} (c : CSS.Checks K D q s r) :
    coordinatePhysicalProfile K Λ e c ≅ Profile.S_X (physicalChecks K Λ e c) :=
  RingChange.profileIso (ringCoordinates K Λ e)
    (projectiveResolution (conjugateS K Λ (LatticeCompatibility.reduced K Λ c))) ≪≫
      ResolutionComparison.profileIsoOfModuleIso (ModuleCat.of (Laurent K D) (Laurent K D))
        _ (conjugateReducedRenameIso K Λ e c) (Profile.resolution (physicalChecks K Λ e c))

/-- Restriction along the exact original-lattice inclusion is the native
profile of the actual physically coarse-grained CSS checks. -/
def physicalChecksRestrictionIso {q s r : ℕ} (c : CSS.Checks K D q s r) :
    (ModuleCat.restrictScalars (coordinateEmbedding K Λ e)).mapDerivedCategory.obj
      (Profile.S_X c) ≅ Profile.S_X (physicalChecks K Λ e c) :=
  coordinatePhysicalProfileIso K Λ e c ≪≫ physicalChecksProfileIso K Λ e c

/-- Exactly k scaling steps, exactly p^k Lambda, and the native profile of
the actual finite check matrices on that lattice. -/
def iteratedPhysicalChecksProfileIso (p k : ℕ) (hp : p ≠ 0)
    {q s r : ℕ} (c : CSS.Checks K D q s r) :
    (ExactIteration.derived (ModuleCat.restrictScalars (Koszul.scaling K D p)) k).obj
      ((ModuleCat.restrictScalars (coordinateEmbedding K Λ e)).mapDerivedCategory.obj
        (Profile.S_X c)) ≅
      (by
        letI := LatticeBasis.scaled_finiteIndex Λ (pow_ne_zero k hp)
        exact Profile.S_X (physicalChecks K (LatticeBasis.scaled Λ (p ^ k))
          (scaledCoordinates Λ e (p ^ k) (pow_ne_zero k hp)) c)) := by
  letI := LatticeBasis.scaled_finiteIndex Λ (pow_ne_zero k hp)
  exact iteratedPhysicalProfileIso K Λ e p k hp c ≪≫
    physicalChecksProfileIso K (LatticeBasis.scaled Λ (p ^ k))
      (scaledCoordinates Λ e (p ^ k) (pow_ne_zero k hp)) c

end
end Decoupling.HighDim.ScalingLattice
