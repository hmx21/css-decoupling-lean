import Decoupling.HighDim.KoszulExact
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# The Laurent Koszul complex as a native projective resolution

Source: `drafts/main.tex:370–382`. The target is the coefficient module with
its actual augmentation action. The projective resolution below uses the
ordered-cell complex and its proved exactness; no resolution or exactness
certificate is an input.
-/

namespace Decoupling.HighDim.Koszul

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (K : Type*) [CommRing K] (D : ℕ)

/-- The coefficient module with the actual Laurent augmentation action. -/
def coefficientModule : ModuleCat (Laurent K D) :=
  (ModuleCat.restrictScalars augmentation).obj (ModuleCat.of K K)

/-- The augmentation on the actual degree-zero cell module. -/
def augmentationMap : (laurentComplex K D).X 0 ⟶ coefficientModule K D :=
  ModuleCat.ofHom (X := (laurentComplex K D).X 0)
    (Y := coefficientModule K D) {
    toFun v := (show K from augmentation (zeroTermEquiv (Laurent K D) v))
    map_add' v w := by
      change augmentation (zeroTermEquiv (Laurent K D) (v + w)) =
        augmentation (zeroTermEquiv (Laurent K D) v) +
          augmentation (zeroTermEquiv (Laurent K D) w)
      rw [map_add, map_add]
    map_smul' r v := by
      change augmentation (zeroTermEquiv (Laurent K D) (r • v)) =
        augmentation r * augmentation (zeroTermEquiv (Laurent K D) v)
      rw [map_smul, smul_eq_mul, map_mul] }

@[simp] theorem augmentationMap_apply (v : Term (Laurent K D) D 0) :
    augmentationMap K D v = augmentation (zeroTermEquiv (Laurent K D) v) := rfl

theorem boundary_augmentation :
    (laurentComplex K D).d 1 0 ≫ augmentationMap K D = 0 := by
  ext v
  change augmentation (zeroTermEquiv (Laurent K D) ((laurentComplex K D).d 1 0 v)) = 0
  simp only [laurentComplex, complex_d]
  exact (laurent_exact_at_zero K D _).mpr ⟨v, rfl⟩

/-- The actual augmented chain map to the coefficient module in degree zero. -/
def resolutionAugmentation : laurentComplex K D ⟶
    (ChainComplex.single₀ (ModuleCat (Laurent K D))).obj (coefficientModule K D) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨augmentationMap K D, boundary_augmentation K D⟩

@[simp] theorem resolutionAugmentation_zero :
    (resolutionAugmentation K D).f 0 = augmentationMap K D :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

variable [IsDomain K]

theorem laurentComplex_exactAt_succ (k : ℕ) :
    (laurentComplex K D).ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k (by simp) (by simp)]
  rw [ShortComplex.moduleCat_exact_iff]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    laurentComplex, complex_d]
  change ∀ v : Term (Laurent K D) D (k + 1),
    (boundary (Laurent K D) (difference K) k).hom v = 0 →
    ∃ z, (boundary (Laurent K D) (difference K) (k + 1)).hom z = v
  exact laurent_exact K D k

instance resolutionAugmentation_quasiIso : QuasiIso (resolutionAugmentation K D) :=
  ⟨fun k => by
    cases k with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff]
      rw [ShortComplex.quasiIso_iff_of_zeros' _ (by rfl)
        (by change ((ChainComplex.single₀ (ModuleCat (Laurent K D))).obj
          (coefficientModule K D)).d 1 0 = 0; simp) (by rfl)]
      constructor
      · rw [ShortComplex.moduleCat_exact_iff]
        simp only [HomologicalComplex.shortComplexFunctor', laurentComplex, complex_d,
          resolutionAugmentation_zero]
        intro v hv
        exact (laurent_exact_at_zero K D v).mp hv
      · apply (ModuleCat.epi_iff_surjective _).mpr
        simp only [HomologicalComplex.shortComplexFunctor', resolutionAugmentation_zero]
        change Function.Surjective (fun v : Term (Laurent K D) D 0 =>
          (augmentation (zeroTermEquiv (Laurent K D) v) : K))
        exact laurent_augmentation_surjective K D
    | succ k =>
      rw [quasiIsoAt_iff_exactAt']
      · exact laurentComplex_exactAt_succ K D k
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

/-- The genuine mathlib projective resolution computed by the signed Laurent
Koszul complex in every finite dimension over any domain. -/
def projectiveResolution : ProjectiveResolution (coefficientModule K D) where
  complex := laurentComplex K D
  projective k := by
    change Projective (ModuleCat.of (Laurent K D) (Term (Laurent K D) D k))
    exact ModuleCat.projective_of_free (Finsupp.basisSingleOne)
  π := resolutionAugmentation K D

end
end Decoupling.HighDim.Koszul
