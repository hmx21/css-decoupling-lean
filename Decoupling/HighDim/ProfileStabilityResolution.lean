import Decoupling.HighDim.ProfileStability
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Adding a projective summand to an actual resolution

The extra summand occurs only in degree zero. Its augmentation is the
identity, and all exactness assertions are proved from the original native
resolution, without adding an exactness or comparison hypothesis.
-/

namespace Decoupling.HighDim.ProfileStability

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] {X : ModuleCat R}
  (P : ProjectiveResolution X) (T : ModuleCat R)

abbrev productModule := ModuleCat.of R (X × T)

def enlargedTerm : ℕ → ModuleCat R
  | 0 => ModuleCat.of R (P.complex.X 0 × T)
  | n + 1 => P.complex.X (n + 1)

def enlargedDifferential : ∀ n, enlargedTerm P T (n + 1) ⟶ enlargedTerm P T n
  | 0 => ModuleCat.ofHom ((P.complex.d 1 0).hom.prod 0)
  | n + 1 => P.complex.d (n + 2) (n + 1)

theorem enlargedDifferential_squared (n : ℕ) :
    enlargedDifferential P T (n + 1) ≫ enlargedDifferential P T n = 0 := by
  cases n with
  | zero =>
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    apply Prod.ext
    · exact congrArg (fun f : P.complex.X 2 ⟶ P.complex.X 0 => f v)
        (P.complex.d_comp_d 2 1 0)
    · rfl
  | succ n => exact P.complex.d_comp_d (n + 3) (n + 2) (n + 1)

def enlargedComplex : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (enlargedTerm P T) (enlargedDifferential P T)
    (enlargedDifferential_squared P T)

@[simp] theorem enlargedComplex_X (n : ℕ) :
    (enlargedComplex P T).X n = enlargedTerm P T n := rfl
@[simp] theorem enlargedComplex_d (n : ℕ) :
    (enlargedComplex P T).d (n + 1) n = enlargedDifferential P T n := by
  simp [enlargedComplex]

def enlargedEpsilon : (enlargedComplex P T).X 0 ⟶ productModule (X := X) T :=
  ModuleCat.ofHom ((P.π.f 0).hom.prodMap (LinearMap.id : T →ₗ[R] T))

theorem enlargedDifferential_epsilon :
    (enlargedComplex P T).d 1 0 ≫ enlargedEpsilon P T = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  apply Prod.ext
  · exact congrArg (fun f : P.complex.X 1 ⟶ X => f v) P.complex_d_comp_π_f_zero
  · rfl

def enlargedAugmentation : enlargedComplex P T ⟶
    (ChainComplex.single₀ (ModuleCat R)).obj (productModule (X := X) T) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨enlargedEpsilon P T, enlargedDifferential_epsilon P T⟩

@[simp] theorem enlargedAugmentation_zero :
    (enlargedAugmentation P T).f 0 = enlargedEpsilon P T :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

theorem enlargedComplex_exactAt (n : ℕ) : (enlargedComplex P T).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  simp only [ShortComplex.moduleCat_exact_iff, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor', enlargedComplex_d]
  intro v hv
  have hP := (ShortComplex.moduleCat_exact_iff _).mp (P.exact_succ n)
  cases n with
  | zero => exact hP v (congrArg Prod.fst hv)
  | succ n => exact hP v hv

instance enlargedAugmentation_quasiIso : QuasiIso (enlargedAugmentation P T) :=
  ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff]
      rw [ShortComplex.quasiIso_iff_of_zeros' _ (by rfl)
        (by change ((ChainComplex.single₀ (ModuleCat R)).obj
          (productModule (X := X) T)).d 1 0 = 0; simp) (by rfl)]
      constructor
      · rw [ShortComplex.moduleCat_exact_iff]
        simp only [HomologicalComplex.shortComplexFunctor', enlargedComplex_d,
          enlargedAugmentation_zero]
        intro v hv
        obtain ⟨u, hu⟩ := (ShortComplex.moduleCat_exact_iff _).mp P.exact₀ v.1
          (congrArg Prod.fst hv)
        exact ⟨u, Prod.ext hu (congrArg Prod.snd hv).symm⟩
      · apply (ModuleCat.epi_iff_surjective _).mpr
        simp only [HomologicalComplex.shortComplexFunctor', enlargedAugmentation_zero]
        intro v
        obtain ⟨u, hu⟩ := (ModuleCat.epi_iff_surjective (P.π.f 0)).mp inferInstance v.1
        exact ⟨(u, v.2), Prod.ext hu rfl⟩
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact enlargedComplex_exactAt P T n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

variable [Projective T]

/-- A native projective resolution of the actual direct product X × T. -/
def enlargedResolution : ProjectiveResolution (productModule (X := X) T) where
  complex := enlargedComplex P T
  projective n := by
    cases n with
    | zero =>
      change Projective (ModuleCat.of R (P.complex.X 0 × T))
      let : Module.Projective R (P.complex.X 0) := ModuleCat.projective_of_module_projective _
      let : Module.Projective R T := ModuleCat.projective_of_module_projective _
      exact ModuleCat.projective_of_categoryTheory_projective _
    | succ n => exact P.projective (n + 1)
  π := enlargedAugmentation P T

end
end Decoupling.HighDim.ProfileStability
