import Decoupling.HighDim.ProfileStabilityResolution
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Finite products of actual projective resolutions

Dependency of the HD008 toric-stack native-profile bridge. The augmented
complex is defined degree by degree on the actual product modules, and its
exactness and projectivity are proved. No splitting hypothesis is used.
-/

namespace Decoupling.HighDim.PiResolution

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] {ι : Type}
  {X : ι → ModuleCat R} (P : ∀ i, ProjectiveResolution (X i))

abbrev module := ModuleCat.of R (∀ i, X i)

def differential (n : ℕ) :
    ModuleCat.of R (∀ i, (P i).complex.X (n + 1)) ⟶
      ModuleCat.of R (∀ i, (P i).complex.X n) :=
  ModuleCat.ofHom (LinearMap.pi (fun i => ((P i).complex.d (n + 1) n).hom.comp
    (LinearMap.proj i)))

@[simp] theorem differential_apply (n : ℕ) (v : ∀ i, (P i).complex.X (n + 1)) (i : ι) :
    differential P n v i = (P i).complex.d (n + 1) n (v i) := rfl

theorem differential_squared (n : ℕ) : differential P (n + 1) ≫ differential P n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  funext i
  exact congrArg (fun f => f (v i)) ((P i).complex.d_comp_d (n + 2) (n + 1) n)

def complex : ChainComplex (ModuleCat R) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of R (∀ i, (P i).complex.X n))
    (differential P) (differential_squared P)

@[simp] theorem complex_X (n : ℕ) :
    (complex P).X n = ModuleCat.of R (∀ i, (P i).complex.X n) := rfl

@[simp] theorem complex_d (n : ℕ) : (complex P).d (n + 1) n = differential P n := by
  simp [complex]

def epsilon : (complex P).X 0 ⟶ module (X := X) :=
  ModuleCat.ofHom (LinearMap.pi (fun i => ((P i).π.f 0).hom.comp (LinearMap.proj i)))

theorem differential_epsilon : (complex P).d 1 0 ≫ epsilon P = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  funext i
  exact congrArg (fun f => f (v i)) (P i).complex_d_comp_π_f_zero

def augmentation : complex P ⟶ (ChainComplex.single₀ (ModuleCat R)).obj (module (X := X)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨epsilon P, differential_epsilon P⟩

@[simp] theorem augmentation_zero : (augmentation P).f 0 = epsilon P :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

theorem exactAt (n : ℕ) : (complex P).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  simp only [ShortComplex.moduleCat_exact_iff, HomologicalComplex.sc',
    HomologicalComplex.shortComplexFunctor', complex_d]
  intro v hv
  have h (i : ι) := (ShortComplex.moduleCat_exact_iff _).mp ((P i).exact_succ n)
    (v i) (congrFun hv i)
  choose u hu using h
  exact ⟨u, funext hu⟩

instance augmentation_quasiIso : QuasiIso (augmentation P) :=
  ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff]
      rw [ShortComplex.quasiIso_iff_of_zeros' _ (by rfl)
        (by change ((ChainComplex.single₀ (ModuleCat R)).obj
          (module (X := X))).d 1 0 = 0; simp) (by rfl)]
      constructor
      · rw [ShortComplex.moduleCat_exact_iff]
        simp only [HomologicalComplex.shortComplexFunctor', complex_d, augmentation_zero]
        intro v hv
        have h (i : ι) := (ShortComplex.moduleCat_exact_iff _).mp (P i).exact₀
          (v i) (congrFun hv i)
        choose u hu using h
        exact ⟨u, funext hu⟩
      · apply (ModuleCat.epi_iff_surjective _).mpr
        simp only [HomologicalComplex.shortComplexFunctor', augmentation_zero]
        intro v
        have h (i : ι) := (ModuleCat.epi_iff_surjective ((P i).π.f 0)).mp inferInstance (v i)
        choose u hu using h
        exact ⟨u, funext hu⟩
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact exactAt P n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

variable [Fintype ι]

/-- The finite product is projective in every degree, including an empty index set. -/
def resolution : ProjectiveResolution (module (X := X)) where
  complex := complex P
  projective n := by
    change Projective (ModuleCat.of R (∀ i, (P i).complex.X n))
    exact Projective.of_iso (ModuleCat.biproductIsoPi (fun i => (P i).complex.X n)) inferInstance
  π := augmentation P

end
end Decoupling.HighDim.PiResolution
