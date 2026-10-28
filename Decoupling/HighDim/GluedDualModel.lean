import Decoupling.HighDim.GluedResolution

/-!
# The actual nonnegative dual model of the glued example

Its two differentials are exactly the displayed X checks and their
metacheck. The derived comparison with `S_X` retains the extension class.
-/

namespace Decoupling.HighDim.Glued

open CategoryTheory CategoryTheory.Limits Matrix HomologicalComplex
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

def rightD : (n : ℕ) → resolutionTerm K n ⟶ resolutionTerm K (n + 1)
  | 0 => ModuleCat.ofHom (xChecks K).mulVecLin
  | 1 => ModuleCat.ofHom (metacheck K).mulVecLin
  | _ + 2 => 0

theorem rightD_sq (n : ℕ) : rightD K n ≫ rightD K (n + 1) = 0 := by
  rcases n with _ | (_ | n)
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change metacheck K *ᵥ (xChecks K *ᵥ v) = 0
    rw [Matrix.mulVec_mulVec, metacheck_comp, Matrix.zero_mulVec]
  · simp [rightD]
  · simp [rightD]

def rightComplex : CochainComplex (ModuleCat (Laurent K 3)) ℕ :=
  CochainComplex.of (resolutionTerm K) (rightD K) (rightD_sq K)

def dualComplex : CochainComplex (ModuleCat (Laurent K 3)) ℕ :=
  ResolutionCohomology.dualComplex (conjugateResolution K)
    (ModuleCat.of (Laurent K 3) (Laurent K 3))

def dualCoordinates (n : ℕ) : (dualComplex K).X n ≃ₗ[Laurent K 3]
    (Fin (resolutionRank n) → Laurent K 3) := FiniteResolution.dualFreeCoordinates _

theorem dualCoordinates_comm (n : ℕ) (v : (dualComplex K).X n) :
    dualCoordinates K (n + 1) ((dualComplex K).d n (n + 1) v) =
      rightD K n (dualCoordinates K n v) := by
  rcases n with _ | (_ | n)
  · change FiniteResolution.dualFreeCoordinates 4
      (FiniteResolution.conjugateMatrixMap (dagger (xChecks K)) ≫ v) =
        xChecks K *ᵥ FiniteResolution.dualFreeCoordinates 6 v
    rw [FiniteResolution.dualFreeCoordinates_precomp, dagger_dagger]
  · change FiniteResolution.dualFreeCoordinates 1
      (FiniteResolution.conjugateMatrixMap (dagger (metacheck K)) ≫ v) =
        metacheck K *ᵥ FiniteResolution.dualFreeCoordinates 4 v
    rw [FiniteResolution.dualFreeCoordinates_precomp, dagger_dagger]
  · change (_ : Fin 0 → Laurent K 3) = _
    exact Subsingleton.elim _ _

def dualRightIso : dualComplex K ≅ rightComplex K :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (dualCoordinates K n).toModuleIso)
    (fun n m hnm => by
      change n + 1 = m at hnm
      subst m
      rw [show (rightComplex K).d n (n + 1) = rightD K n from CochainComplex.of_d _ _ _]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro v
      change rightD K n (dualCoordinates K n v) =
        dualCoordinates K (n + 1) ((dualComplex K).d n (n + 1) v)
      exact (dualCoordinates_comm K n v).symm)

def nativeRightProfileIso :
    DerivedCategory.Q.obj (CochainComplex.truncGE
      ((rightComplex K).extend ComplexShape.embeddingUpNat) 1) ≅
      Profile.S_X (checks K) :=
  DerivedCategory.Q.mapIso
    (((ComplexShape.embeddingUpIntGE 1).truncGEFunctor (ModuleCat (Laurent K 3))).mapIso
      ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat (Laurent K 3))).mapIso
        (dualRightIso K).symm)) ≪≫ nativeProfileIso K

end
end Decoupling.HighDim.Glued
