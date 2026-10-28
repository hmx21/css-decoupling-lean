import Decoupling.HighDim.RingDimension
import Decoupling.HighDim.Laurent
import Mathlib.CategoryTheory.Abelian.Projective.Resolution
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.RingTheory.Finiteness.Cardinality
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Constructing bounded resolutions with finite terms

Source: `drafts/appendix.tex`, C1, lines 353–364. The augmentation and all
differentials below are actual module maps, with exactness stated using
their actual ranges and kernels. A finite free cover is chosen at each
stage; its actual kernel gives the next syzygy. The resulting data is
converted to mathlib's native `ProjectiveResolution`.
-/

namespace Decoupling.HighDim.FiniteResolution

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u
variable {R : Type u} [CommRing R]

/-- Concrete bounded augmented resolution data. The exactness fields are
properties of the actual differentials, not a definition of derived Ext. -/
structure Data (M : ModuleCat.{u} R) (length : ℕ) where
  X : ℕ → ModuleCat.{u} R
  d : ∀ n, X (n + 1) ⟶ X n
  sq : ∀ n, d (n + 1) ≫ d n = 0
  ε : X 0 ⟶ M
  d_ε : d 0 ≫ ε = 0
  surjective : Function.Surjective ε.hom
  exact_zero : LinearMap.range (d 0).hom = LinearMap.ker ε.hom
  exact_succ : ∀ n, LinearMap.range (d (n + 1)).hom = LinearMap.ker (d n).hom
  projective : ∀ n, Projective (X n)
  finite : ∀ n, Module.Finite R (X n)
  zero_above : ∀ n, length < n → IsZero (X n)

attribute [instance] Data.projective Data.finite

noncomputable section

/-- An explicit zero module in the same universe as the ring. -/
abbrev ZeroModule (R : Type u) [CommRing R] : ModuleCat.{u} R :=
  ModuleCat.of R (Fin 0 → R)

/-- A finite projective module has a length-zero resolution. -/
def self (M : ModuleCat.{u} R) [Projective M] [Module.Finite R M] : Data M 0 where
  X n := match n with | 0 => M | _ + 1 => ZeroModule R
  d _ := 0
  sq _ := by simp
  ε := 𝟙 M
  d_ε := by simp
  surjective := Function.surjective_id
  exact_zero := by simp
  exact_succ _ := by
    apply Subsingleton.elim
  projective n := by cases n <;> infer_instance
  finite n := by cases n <;> infer_instance
  zero_above n hn := by
    cases n with
    | zero => omega
    | succ n => exact ModuleCat.isZero_of_subsingleton _

variable {M P : ModuleCat.{u} R} (p : P ⟶ M)

/-- The actual kernel of a proposed finite cover. -/
abbrev Syzygy := ModuleCat.of R (LinearMap.ker p.hom)

/-- The elementary short exact sequence used at every recursive step. -/
def kernelSequence : ShortComplex (ModuleCat.{u} R) :=
  ShortComplex.moduleCatMk (LinearMap.ker p.hom).subtype p.hom (by ext x; exact x.property)

theorem kernelSequence_shortExact (hp : Function.Surjective p.hom) :
    (kernelSequence p).ShortExact where
  exact := by
    apply (ShortComplex.moduleCat_exact_iff _).mpr
    intro x hx
    exact ⟨⟨x, hx⟩, rfl⟩
  mono_f := (ModuleCat.mono_iff_injective _).mpr (LinearMap.ker p.hom).injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr hp

/-- A finite free cover lowers the native projective-dimension bound. -/
theorem syzygy_projectiveDimensionLE (hp : Function.Surjective p.hom)
    [Projective P] (n : ℕ) [HasProjectiveDimensionLE M (n + 1)] :
    HasProjectiveDimensionLE (Syzygy p) n := by
  have hpP : Projective (kernelSequence p).X₂ := by
    change Projective P
    infer_instance
  have hpM : HasProjectiveDimensionLT (kernelSequence p).X₃ (n + 2) := by
    change HasProjectiveDimensionLE M (n + 1)
    infer_instance
  exact ((kernelSequence_shortExact p hp).hasProjectiveDimensionLT_X₃_iff n hpP).mp hpM

/-- Prepend the actual cover `P → M` to a resolution of its actual kernel.
This is the operation needed later to retain a prescribed CSS prefix. -/
def prepend {n : ℕ} (hp : Function.Surjective p.hom)
    [Projective P] [Module.Finite R P] (A : Data (Syzygy p) n) : Data M (n + 1) where
  X k := match k with | 0 => P | k + 1 => A.X k
  d k := match k with
    | 0 => A.ε ≫ ModuleCat.ofHom (LinearMap.ker p.hom).subtype
    | k + 1 => A.d k
  sq k := by
    cases k with
    | zero => simp only [← Category.assoc, A.d_ε, zero_comp]
    | succ k => exact A.sq k
  ε := p
  d_ε := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (A.ε x).property
  surjective := hp
  exact_zero := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact (A.ε y).property
    · intro hx
      obtain ⟨y, hy⟩ := A.surjective ⟨x, hx⟩
      exact ⟨y, congrArg Subtype.val hy⟩
  exact_succ k := by
    cases k with
    | zero =>
      rw [A.exact_zero]
      ext x
      change A.ε x = 0 ↔ (A.ε x : P) = 0
      exact ⟨fun hx => congrArg Subtype.val hx, fun hx => Subtype.ext hx⟩
    | succ k => exact A.exact_succ k
  projective k := by cases k <;> infer_instance
  finite k := by cases k <;> infer_instance
  zero_above k hk := by
    cases k with
    | zero => omega
    | succ k => exact A.zero_above k (by omega)

/-- Every finite module over a Noetherian ring with projective dimension at
most `n` has a bounded resolution by finite projective modules. All covers
except possibly the last term are finite free by construction. -/
theorem exists_data [IsNoetherianRing R] (n : ℕ) (M : ModuleCat.{u} R)
    [Module.Finite R M] [HasProjectiveDimensionLE M n] : Nonempty (Data M n) := by
  induction n generalizing M with
  | zero =>
    have : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).mpr inferInstance
    exact ⟨self M⟩
  | succ n ih =>
    obtain ⟨k, f, hf⟩ := Module.Finite.exists_fin' R M
    let p : ModuleCat.of R (Fin k → R) ⟶ M := ModuleCat.ofHom f
    have : HasProjectiveDimensionLE (Syzygy p) n := syzygy_projectiveDimensionLE p hf n
    obtain ⟨A⟩ := ih (Syzygy p)
    exact ⟨prepend p hf A⟩

namespace Data

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {M : ModuleCat.{u} R} {n : ℕ} (A : Data M n)

/-- The native chain complex determined by the constructed maps. -/
def complex : ChainComplex (ModuleCat.{u} R) ℕ := ChainComplex.of A.X A.d A.sq

@[simp] theorem complex_X (k : ℕ) : A.complex.X k = A.X k := rfl

@[simp] theorem complex_d (k : ℕ) : A.complex.d (k + 1) k = A.d k :=
  ChainComplex.of_d _ _ k

/-- The actual augmentation as a map of native chain complexes. -/
def augmentation : A.complex ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj M :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨A.ε, by simpa using A.d_ε⟩

@[simp] theorem augmentation_zero : A.augmentation.f 0 = A.ε :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

theorem complex_exactAt_succ (k : ℕ) : A.complex.ExactAt (k + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (k + 2) (k + 1) k (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    complex_d] using A.exact_succ k

instance augmentation_quasiIso : QuasiIso A.augmentation := ⟨fun k => by
  cases k with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff]
    rw [ShortComplex.quasiIso_iff_of_zeros' _ (by rfl)
      (by change ((ChainComplex.single₀ (ModuleCat.{u} R)).obj M).d 1 0 = 0; simp)
      (by rfl)]
    constructor
    · apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
      simpa [HomologicalComplex.shortComplexFunctor'] using A.exact_zero
    · apply (ModuleCat.epi_iff_surjective _).mpr
      simpa [HomologicalComplex.shortComplexFunctor'] using A.surjective
  | succ k =>
    rw [quasiIsoAt_iff_exactAt']
    · exact A.complex_exactAt_succ k
    · exact ChainComplex.exactAt_succ_single_obj _ _⟩

/-- The constructed data is a native projective resolution, including its
actual augmentation quasi-isomorphism. -/
def toProjectiveResolution : ProjectiveResolution M where
  complex := A.complex
  projective k := A.projective k
  π := A.augmentation

end Data

/-- A native projective resolution with finite terms and an explicit bound. -/
theorem exists_native [IsNoetherianRing R] (n : ℕ) (M : ModuleCat.{u} R)
    [Module.Finite R M] [HasProjectiveDimensionLE M n] :
    ∃ A : ProjectiveResolution M,
      (∀ k, Module.Finite R (A.complex.X k)) ∧
      (∀ k, n < k → IsZero (A.complex.X k)) := by
  obtain ⟨A⟩ := exists_data n M
  exact ⟨A.toProjectiveResolution, A.finite, A.zero_above⟩

end

end Decoupling.HighDim.FiniteResolution
