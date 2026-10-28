import Decoupling.HighDim.GluedNativeCone

/-!
# The actual homology of the coupling cone

The two coefficient layers and their augmentation action are consequences
of the actual distinguished triangle and its long exact homology sequence.
-/

namespace Decoupling.HighDim.Glued
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open PostnikovInduction
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

theorem couplingTriangleLeft_zero (n : ℤ) (hn : n ≠ 1) :
    IsZero (H (couplingTriangle K).obj₁ n) := by
  change IsZero ((DerivedCategory.homologyFunctor (ModuleCat (Laurent K 3)) n).obj
    ((DerivedCategory.singleFunctor (ModuleCat (Laurent K 3)) 1).obj (Koszul.coefficientModule K 3)))
  rcases lt_or_gt_of_ne hn with h | h
  · exact DerivedCategory.isZero_of_isGE _ 1 n h
  · exact DerivedCategory.isZero_of_isLE _ 1 n h

theorem couplingTriangleRight_zero (n : ℤ) (hn : n ≠ 2) :
    IsZero (H (couplingTriangle K).obj₃ n) := by
  apply IsZero.of_iso _ ((DerivedCategory.homologyFunctor (ModuleCat (Laurent K 3)) n).mapIso
    (couplingTriangleRightIso K))
  rcases lt_or_gt_of_ne hn with h | h
  · exact DerivedCategory.isZero_of_isGE _ 2 n h
  · exact DerivedCategory.isZero_of_isLE _ 2 n h

theorem couplingCone_supported : Supported (DerivedCategory.Q.obj (couplingCone K)) {1, 2} := by
  intro n hn
  have hn1 : n ≠ 1 := by simpa using fun h => hn (by simp [h])
  have hn2 : n ≠ 2 := by simpa using fun h => hn (by simp [h])
  exact (DerivedCategory.HomologySequence.exact₂ (couplingTriangle K)
    (couplingTriangle_distinguished K) n).isZero_X₂
      ((couplingTriangleLeft_zero K n hn1).eq_of_src _ _)
      ((couplingTriangleRight_zero K n hn2).eq_of_tgt _ _)

instance couplingCone_isGE : (couplingCone K).IsGE 1 := by
  rw [← DerivedCategory.isGE_Q_obj_iff]
  exact supported_isGE (couplingCone_supported K) 1 (by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    omega)

instance couplingCone_isLE : (couplingCone K).IsLE 2 := by
  rw [← DerivedCategory.isLE_Q_obj_iff]
  exact supported_isLE (couplingCone_supported K) 2 (by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    omega)

theorem couplingTriangle_mor1_homology_isIso :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat (Laurent K 3)) 1).map
      (couplingTriangle K).mor₁) := by
  have hm : Mono ((DerivedCategory.homologyFunctor (ModuleCat (Laurent K 3)) 1).map
      (couplingTriangle K).mor₁) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff (couplingTriangle K)
      (couplingTriangle_distinguished K) 0 1 (by omega)).mpr
        ((couplingTriangleRight_zero K 0 (by omega)).eq_of_src _ _)
  have he : Epi ((DerivedCategory.homologyFunctor (ModuleCat (Laurent K 3)) 1).map
      (couplingTriangle K).mor₁) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff (couplingTriangle K)
      (couplingTriangle_distinguished K) 1).mpr
        ((couplingTriangleRight_zero K 1 (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

theorem couplingTriangle_mor2_homology_isIso :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat (Laurent K 3)) 2).map
      (couplingTriangle K).mor₂) := by
  have hm : Mono ((DerivedCategory.homologyFunctor (ModuleCat (Laurent K 3)) 2).map
      (couplingTriangle K).mor₂) :=
    (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff (couplingTriangle K)
      (couplingTriangle_distinguished K) 2).mpr
        ((couplingTriangleLeft_zero K 2 (by omega)).eq_of_src _ _)
  have he : Epi ((DerivedCategory.homologyFunctor (ModuleCat (Laurent K 3)) 2).map
      (couplingTriangle K).mor₂) :=
    (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff (couplingTriangle K)
      (couplingTriangle_distinguished K) 2 3 (by omega)).mpr
        ((couplingTriangleLeft_zero K 3 (by omega)).eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

def couplingCone_layerOneIso : H (DerivedCategory.Q.obj (couplingCone K)) 1 ≅
    Koszul.coefficientModule K 3 := by
  letI := couplingTriangle_mor1_homology_isIso K
  exact (asIso ((DerivedCategory.homologyFunctor (ModuleCat (Laurent K 3)) 1).map
    (couplingTriangle K).mor₁)).symm ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat (Laurent K 3)) 1).app _

def couplingCone_layerTwoIso : H (DerivedCategory.Q.obj (couplingCone K)) 2 ≅
    Koszul.coefficientModule K 3 := by
  letI := couplingTriangle_mor2_homology_isIso K
  exact asIso ((DerivedCategory.homologyFunctor (ModuleCat (Laurent K 3)) 2).map
    (couplingTriangle K).mor₂) ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat (Laurent K 3)) 2).mapIso
        (couplingTriangleRightIso K) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat (Laurent K 3)) 2).app _

end
end Decoupling.HighDim.Glued
