import Decoupling.HighDim.Profile

/-!
# Independence of the projective-resolution model

This module dualizes actual comparison maps and their actual chain
homotopies. Thus the chosen RHom/profile object is independent of a
resolution, without assuming that a list of matching cohomology groups
determines a derived object.
-/

namespace Decoupling.HighDim.ResolutionComparison

open CategoryTheory CategoryTheory.Abelian
open HomologicalComplex

noncomputable section
attribute [local instance] HasDerivedCategory.standard

variable {R : Type} [CommRing R] (Y : ModuleCat R)
  {C T : ChainComplex (ModuleCat R) ℕ}

/-- Contravariant precomposition on all terms of the actual Hom complex. -/
def dualMap (f : C ⟶ T) : T.linearYonedaObj R Y ⟶ C.linearYonedaObj R Y :=
  (unopFunctor (ModuleCat R) (ComplexShape.down ℕ)).map
    ((((linearYoneda R (ModuleCat R)).obj Y).rightOp.mapHomologicalComplex _).map f).op

@[simp]
theorem dualMap_id (C : ChainComplex (ModuleCat R) ℕ) :
    dualMap Y (𝟙 C) = 𝟙 (C.linearYonedaObj R Y) := by
  simp [dualMap]
  rfl

@[simp]
theorem dualMap_comp {V : ChainComplex (ModuleCat R) ℕ} (f : C ⟶ T) (g : T ⟶ V) :
    dualMap Y (f ≫ g) = dualMap Y g ≫ dualMap Y f := by
  simp [dualMap]
  rfl

/-- Homotopies themselves, rather than only induced cohomology maps, dualize. -/
def dualHomotopy {f g : C ⟶ T} (h : Homotopy f g) :
    Homotopy (dualMap Y f) (dualMap Y g) :=
  ((((linearYoneda R (ModuleCat R)).obj Y).rightOp).mapHomotopy h).unop

def dualHomotopyEquiv (h : HomotopyEquiv C T) :
    HomotopyEquiv (C.linearYonedaObj R Y) (T.linearYonedaObj R Y) where
  hom := dualMap Y h.inv
  inv := dualMap Y h.hom
  homotopyHomInvId := by
    simpa only [dualMap_comp, dualMap_id] using dualHomotopy Y h.homotopyHomInvId
  homotopyInvHomId := by
    simpa only [dualMap_comp, dualMap_id] using dualHomotopy Y h.homotopyInvHomId

variable {X : ModuleCat R} (P Q : ProjectiveResolution X)

/-- Native projective-resolution comparison supplies all the homotopies. -/
def dualResolutionHomotopyEquiv :
    HomotopyEquiv (ResolutionCohomology.dualComplex P Y)
      (ResolutionCohomology.dualComplex Q Y) :=
  dualHomotopyEquiv Y (P.homotopyEquiv Q)

def comparison : ResolutionCohomology.dualComplex P Y ⟶
    ResolutionCohomology.dualComplex Q Y :=
  (dualResolutionHomotopyEquiv Y P Q).hom

instance comparison_quasiIso : QuasiIso (comparison Y P Q) := by
  dsimp [comparison]
  infer_instance

def extendedComparison : Profile.rHomComplex P Y ⟶ Profile.rHomComplex Q Y :=
  extendMap (comparison Y P Q) ComplexShape.embeddingUpNat

instance extendedComparison_quasiIso : QuasiIso (extendedComparison Y P Q) := by
  dsimp [extendedComparison]
  exact (quasiIso_extendMap_iff (comparison Y P Q) ComplexShape.embeddingUpNat).mpr
    (comparison_quasiIso Y P Q)

def positiveComparison : Profile.positiveComplex P Y ⟶ Profile.positiveComplex Q Y :=
  CochainComplex.truncGEMap (extendedComparison Y P Q) 1

instance positiveComparison_quasiIso : QuasiIso (positiveComparison Y P Q) := by
  apply (CochainComplex.quasiIso_truncGEMap_iff (extendedComparison Y P Q) 1).mpr
  intro n _
  have := extendedComparison_quasiIso Y P Q
  exact (quasiIso_iff _).mp this n

/-- Full derived profiles of two resolutions are isomorphic. -/
def profileIso : Profile.ofResolution P Y ≅ Profile.ofResolution Q Y := by
  have : IsIso (DerivedCategory.Q.map (positiveComparison Y P Q)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) _).mpr
      (positiveComparison_quasiIso Y P Q)
  exact @asIso _ _ _ _ (DerivedCategory.Q.map (positiveComparison Y P Q)) this

/-- Transport only the augmentation through a genuine module isomorphism. -/
def transportResolution {N : ModuleCat R} (e : X ≅ N) : ProjectiveResolution N where
  complex := P.complex
  π := P.π ≫ (ChainComplex.single₀ (ModuleCat R)).map e.hom
  quasiIso := by infer_instance

/-- Isomorphic modules have isomorphic full positive RHom profiles. -/
def profileIsoOfModuleIso {N : ModuleCat R} (e : X ≅ N) (Q' : ProjectiveResolution N) :
    Profile.ofResolution P Y ≅ Profile.ofResolution Q' Y :=
  profileIso Y (transportResolution P e) Q'

end
end Decoupling.HighDim.ResolutionComparison
