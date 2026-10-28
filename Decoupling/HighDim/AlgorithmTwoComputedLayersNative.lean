import Decoupling.HighDim.AlgorithmTwoComputedLayersSourceBasis
import Decoupling.HighDim.ToricSplitLayers

/-!
# Native layer coordinates from the computed cohomology bases

The old formal toric multiplicities are not assumed to equal the
computed dimensions. The new coordinate isomorphisms are obtained
from the actual supplied bases of native cohomology. Augmentation
action and vanishing outside the permitted degrees are consequences
of the original formal toric profile.
-/
namespace Decoupling.HighDim.AlgorithmTwoComputedLayers
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgorithmTwoComparison TrivialLayers
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
attribute [local instance] HasDerivedCategory.standard
variable (K : Type) [Field K] (D : ℕ)
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (old : Fin (D - 1) → ℕ)
  (e : DerivedCategory.Q.obj (Toric.stackModel K D (Toric.copyForms D old)) ≅ DerivedCategory.Q.obj C)

def oldTermCohomologyIso (n : ℤ) :
    (stackZeroModel K D (Toric.copyForms D old)).X n ≅ C.homology n :=
  oldZeroCoordinates _ (stackZeroModel_d K D (Toric.copyForms D old))
    ((asIso (DerivedCategory.Q.map (stackAugmentation K D (Toric.copyForms D old)))).symm ≪≫ e) n

include old e

theorem nativeHomology_augmentation (n : ℤ) : AugmentationAction (C.homology n) := by
  apply augmentationAction_of_iso
    (((DerivedCategory.homologyFunctorFactors (ModuleCat (Laurent K D)) n).app C).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat (Laurent K D)) n).mapIso e.symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat (Laurent K D)) n).mapIso
        (Toric.stackDerivedIso K D (Toric.copyForms D old)))
  exact Toric.splitTarget_homology_augmentationAction K D (Toric.copyForms D old) n

theorem nativeHomology_outside (n : ℤ)
    (hn : ¬ ∃ j : Fin (D - 1), (j.val : ℤ) + 1 = n) : IsZero (C.homology n) :=
  (stackZeroModel_outside K D old n hn).of_iso (oldTermCohomologyIso K D old e n).symm

variable (t : Fin (D - 1) → ℕ)
  (basis : ∀ j : Fin (D - 1), Module.Basis (Fin (t j)) K (Layers.coefficients (C.homology (j.val + 1))))

def basisModuleIso (j : Fin (D - 1)) : coefficientVector K D (t j) ≅ C.homology (j.val + 1) :=
  (ModuleCat.restrictScalars augmentation).mapIso (basis j).equivFun.symm.toModuleIso ≪≫
    (coefficientEquiv _ (nativeHomology_augmentation K D old e (j.val + 1))).symm.toModuleIso

theorem basisModuleIso_single (j : Fin (D - 1)) (k : Fin (t j)) :
    (basisModuleIso K D old e t basis j).hom (Pi.single k 1) = basis j k := by
  change (basis j).equivFun.symm (Pi.single k 1) = basis j k
  rw [Module.Basis.equivFun_symm_apply]
  simp [Pi.single_apply]

/-- All integer degrees, with the zero-degree/outside cases proved
from the original formal profile. The choice here only selects a
unique degree label for a proof-level coordinate isomorphism. -/
def nativeCoordinates (n : ℤ) :
    (stackZeroModel K D (Toric.copyForms D t)).X n ≅ C.homology n := by
  classical
  by_cases hn : ∃ j : Fin (D - 1), (j.val : ℤ) + 1 = n
  · let j := hn.choose
    have hj : (j.val : ℤ) + 1 = n := hn.choose_spec
    exact eqToIso (congrArg (stackZeroModel K D (Toric.copyForms D t)).X hj.symm) ≪≫
      sourceCoordinates K D t j ≪≫ basisModuleIso K D old e t basis j ≪≫
        eqToIso (congrArg (fun k : ℤ => C.homology k) hj)
  · exact (stackZeroModel_outside K D t n hn).iso (nativeHomology_outside K D old e n hn)

theorem nativeCoordinates_supported (j : Fin (D - 1)) :
    nativeCoordinates K D old e t basis (j.val + 1) =
      sourceCoordinates K D t j ≪≫ basisModuleIso K D old e t basis j := by
  classical
  unfold nativeCoordinates
  rw [dite_eq_left (show ∃ l : Fin (D - 1), (l.val : ℤ) + 1 = (j.val : ℤ) + 1 from ⟨j, rfl⟩)]
  dsimp only
  have aux (l : Fin (D - 1)) (hl : (l.val : ℤ) + 1 = (j.val : ℤ) + 1) :
      eqToIso (congrArg (stackZeroModel K D (Toric.copyForms D t)).X hl.symm) ≪≫
        sourceCoordinates K D t l ≪≫ basisModuleIso K D old e t basis l ≪≫
          eqToIso (congrArg (fun k : ℤ => C.homology k) hl) =
        sourceCoordinates K D t j ≪≫ basisModuleIso K D old e t basis j := by
    have hj : l = j := by apply Fin.ext; omega
    subst l
    simp
  exact aux _ (Classical.choose_spec
    (show ∃ l : Fin (D - 1), (l.val : ℤ) + 1 = (j.val : ℤ) + 1 from ⟨j, rfl⟩))

theorem nativeCoordinates_top (j : Fin (D - 1)) (k : Fin (t j)) :
    (nativeCoordinates K D old e t basis (j.val + 1)).hom
      (stackTopImage K D (Toric.copyForms D t) ⟨j, k⟩) = basis j k := by
  rw [nativeCoordinates_supported]
  change (basisModuleIso K D old e t basis j).hom
    ((sourceCoordinates K D t j).hom (stackTopImage K D (Toric.copyForms D t) ⟨j, k⟩)) = _
  rw [sourceCoordinates_top, basisModuleIso_single]

end
end Decoupling.HighDim.AlgorithmTwoComputedLayers
