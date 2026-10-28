import Decoupling.HighDim.SingleLayerProfile
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE

/-!
# The canonical Postnikov triangle and its genuine homology layers

These are properties of the canonical t-structure truncations of the
actual derived object. No decomposition or vanishing of gluing is assumed.
-/

namespace Decoupling.HighDim.PostnikovTruncation

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R]

abbrev t := DerivedCategory.TStructure.t (C := ModuleCat R)
abbrev lower (X : DerivedCategory (ModuleCat R)) (n : ℤ) := (t.truncLT n).obj X
abbrev upper (X : DerivedCategory (ModuleCat R)) (n : ℤ) := (t.truncGE n).obj X
abbrev triangle (X : DerivedCategory (ModuleCat R)) (n : ℤ) := (t.triangleLTGE n).obj X

theorem lower_homology_isIso (X : DerivedCategory (ModuleCat R)) (n i : ℤ) (hi : i < n) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map ((t.truncLTι n).app X)) := by
  let T := triangle X n
  have hT := t.triangleLTGE_distinguished n X
  have hm : Mono ((DerivedCategory.homologyFunctor (ModuleCat R) i).map T.mor₁) := by
    apply (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff
      T hT (i - 1) i (by omega)).mpr
    exact (DerivedCategory.isZero_of_isGE (upper X n) n (i - 1) (by omega)).eq_of_src _ _
  have he : Epi ((DerivedCategory.homologyFunctor (ModuleCat R) i).map T.mor₁) := by
    apply (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff T hT i).mpr
    exact (DerivedCategory.isZero_of_isGE (upper X n) n i hi).eq_of_tgt _ _
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map T.mor₁)
  exact isIso_of_mono_of_epi _

def lowerHomologyIso (X : DerivedCategory (ModuleCat R)) (n i : ℤ) (hi : i < n) :
    (DerivedCategory.homologyFunctor (ModuleCat R) i).obj (lower X n) ≅
      (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X := by
  letI := lower_homology_isIso X n i hi
  exact asIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map ((t.truncLTι n).app X))

theorem upper_homology_isIso (X : DerivedCategory (ModuleCat R)) (n i : ℤ) (hi : n ≤ i) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map ((t.truncGEπ n).app X)) := by
  let T := triangle X n
  have hT := t.triangleLTGE_distinguished n X
  have hm : Mono ((DerivedCategory.homologyFunctor (ModuleCat R) i).map T.mor₂) := by
    apply (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff T hT i).mpr
    exact (DerivedCategory.isZero_of_isLE (lower X n) (n - 1) i (by omega)).eq_of_src _ _
  have he : Epi ((DerivedCategory.homologyFunctor (ModuleCat R) i).map T.mor₂) := by
    apply (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT i (i + 1) rfl).mpr
    exact (DerivedCategory.isZero_of_isLE (lower X n) (n - 1) (i + 1) (by omega)).eq_of_tgt _ _
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map T.mor₂)
  exact isIso_of_mono_of_epi _

def upperHomologyIso (X : DerivedCategory (ModuleCat R)) (n i : ℤ) (hi : n ≤ i) :
    (DerivedCategory.homologyFunctor (ModuleCat R) i).obj X ≅
      (DerivedCategory.homologyFunctor (ModuleCat R) i).obj (upper X n) := by
  letI := upper_homology_isIso X n i hi
  exact asIso ((DerivedCategory.homologyFunctor (ModuleCat R) i).map ((t.truncGEπ n).app X))

/-- At the largest possible degree the upper truncation is exactly its
genuine homology module in that degree. -/
def upperSingleIso (X : DerivedCategory (ModuleCat R)) (n : ℤ) [X.IsLE n] :
    upper X n ≅ (DerivedCategory.singleFunctor (ModuleCat R) n).obj
      ((DerivedCategory.homologyFunctor (ModuleCat R) n).obj X) :=
  Profile.singleDegreeIso (upper X n) n ≪≫
    (DerivedCategory.singleFunctor (ModuleCat R) n).mapIso (upperHomologyIso X n n le_rfl).symm

end
end Decoupling.HighDim.PostnikovTruncation
