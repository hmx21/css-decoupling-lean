import Decoupling.HighDim.ToricModel
import Mathlib.Algebra.Homology.Embedding.Restriction
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# The actual tail Koszul resolution of its actual cokernel

Every nonnegative tail is exact in positive degrees, because it retains
all neighboring terms there. Its degree-zero quotient is defined by the
actual first differential and equipped with the native augmentation.
This supplies finite projective resolutions used for independent native
toric-profile identification; no resolution-existence input is needed.
-/

namespace Decoupling.HighDim.Toric

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [CommRing K] (D a : ℕ)

def tailEmbedding (a : ℕ) : (ComplexShape.down ℕ).Embedding (ComplexShape.down ℕ) :=
  ComplexShape.Embedding.mk' _ _ (fun n => a + n)
    (by intro i j h; dsimp at h; omega) (by intro i j; dsimp; omega)

instance (a : ℕ) : (tailEmbedding a).IsRelIff := by
  dsimp [tailEmbedding]
  infer_instance

def tailComplex : ChainComplex (ModuleCat (Laurent K D)) ℕ :=
  (Koszul.laurentComplex K D).restriction (tailEmbedding a)

abbrev TailCokernel := (tailComplex K D a).X 0 ⧸
  LinearMap.range ((tailComplex K D a).d 1 0).hom

def tailProjection : (tailComplex K D a).X 0 ⟶ ModuleCat.of (Laurent K D) (TailCokernel K D a) :=
  ModuleCat.ofHom (LinearMap.range ((tailComplex K D a).d 1 0).hom).mkQ

def tailAugmentation : tailComplex K D a ⟶
    (ChainComplex.single₀ (ModuleCat (Laurent K D))).obj
      (ModuleCat.of (Laurent K D) (TailCokernel K D a)) :=
  (ChainComplex.toSingle₀Equiv _ _).symm ⟨tailProjection K D a, by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩⟩

@[simp] theorem tailAugmentation_zero :
    (tailAugmentation K D a).f 0 = tailProjection K D a :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

variable [IsDomain K]

theorem tailComplex_exact_succ (n : ℕ) : (tailComplex K D a).ExactAt (n + 1) := by
  rw [exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp)]
  have he : (Koszul.laurentComplex K D).ExactAt (a + n + 1) := by
    exact Koszul.laurentComplex_exactAt_succ K D (a + n)
  rw [exactAt_iff' _ (a + n + 2) (a + n + 1) (a + n) (by apply (ComplexShape.down ℕ).prev_eq'; change (a + n + 1) + 1 = a + n + 2; omega)
    (by apply (ComplexShape.down ℕ).next_eq'; change (a + n) + 1 = a + n + 1; omega)] at he
  exact he

instance tailAugmentation_quasiIso : QuasiIso (tailAugmentation K D a) := ⟨fun n => by
  cases n with
  | zero =>
    rw [ChainComplex.quasiIsoAt₀_iff]
    rw [ShortComplex.quasiIso_iff_of_zeros' _
      (by change (tailComplex K D a).d 0 0 = 0; exact (tailComplex K D a).shape _ _ (by simp))
      (by change ((ChainComplex.single₀ (ModuleCat (Laurent K D))).obj
        (ModuleCat.of (Laurent K D) (TailCokernel K D a))).d 1 0 = 0; simp) (by rfl)]
    constructor
    · apply (ShortComplex.moduleCat_exact_iff _).mpr
      intro x hx
      change (LinearMap.range ((tailComplex K D a).d 1 0).hom).mkQ x = 0 at hx
      exact (Submodule.Quotient.mk_eq_zero _).mp hx
    · apply (ModuleCat.epi_iff_surjective _).mpr
      exact (LinearMap.range ((tailComplex K D a).d 1 0).hom).mkQ_surjective
  | succ n =>
    rw [quasiIsoAt_iff_exactAt']
    · exact tailComplex_exact_succ K D a n
    · exact ChainComplex.exactAt_succ_single_obj _ _⟩

instance tailComplex_finite (n : ℕ) : Module.Finite (Laurent K D) ((tailComplex K D a).X n) := by
  let : Module.Finite (Laurent K D) (Laurent K D) := Module.Finite.self _
  change Module.Finite (Laurent K D) (Koszul.Term (Laurent K D) D (a + n))
  infer_instance

instance tailComplex_free (n : ℕ) : Module.Free (Laurent K D) ((tailComplex K D a).X n) := by
  change Module.Free (Laurent K D) (Koszul.Term (Laurent K D) D (a + n))
  infer_instance

def tailResolution : ProjectiveResolution (ModuleCat.of (Laurent K D) (TailCokernel K D a)) where
  complex := tailComplex K D a
  projective n := inferInstance
  π := tailAugmentation K D a

omit [IsDomain K] in
theorem tailComplex_zero_above (n : ℕ) (hn : D < n + a) :
    IsZero ((tailComplex K D a).X n) := by
  let : Subsingleton ((tailComplex K D a).X n) := Koszul.term_subsingleton (Laurent K D) (by change D < a + n; omega)
  exact ModuleCat.isZero_of_subsingleton _

end
end Decoupling.HighDim.Toric
