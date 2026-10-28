import Decoupling.HighDim.ExtRestrictionVanishing
import Mathlib.CategoryTheory.Abelian.Projective.Ext

/-!
# Native Ext classes as unique Koszul cochains

Source: `drafts/main.tex`, Lemma `lem:values`; Appendix B.2.
The maps here are the actual `ProjectiveResolution.extMk` maps for the
proved Laurent Koszul resolution. Their injectivity follows from vanishing
of actual coboundaries, not from a definition of a replacement Ext group.
-/

namespace Decoupling.HighDim.ExtValues

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Preadditive CategoryTheory.Limits
open CochainComplex.HomComplex Koszul
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ}

/-- Every Koszul cochain with augmentation-annihilated target is a cocycle;
the very same identity also says every coboundary is zero. -/
theorem boundary_postcomp_zero (A : ModuleCat (Laurent K D))
    (hA : ∀ i : Fin D, ∀ a : A, difference K i • a = 0)
    (n : ℕ) (f : (laurentComplex K D).X n ⟶ A) :
    (laurentComplex K D).d (n + 1) n ≫ f = 0 := by
  change (complex (Laurent K D) (difference K)).d (n + 1) n ≫ f = 0
  rw [complex_d]
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro I r
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_zero,
    LinearMap.zero_apply]
  change f ((boundary (Laurent K D) (difference K) n).hom (Finsupp.single I r)) = 0
  rw [boundary]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply, map_sum, map_zsmul]
  apply Finset.sum_eq_zero
  intro i _
  change (-1 : ℤ) ^ i.val • f (weightedFace (Laurent K D) (difference K) n i
    (Finsupp.single I r)) = 0
  rw [weightedFace_single, mul_comm r, ← smul_eq_mul, ← Finsupp.smul_single,
    f.hom.map_smul, hA]
  simp

/-- Construct a native Ext class from any actual Koszul cochain. -/
def coefficientMk (A : ModuleCat (Laurent K D))
    (hA : ∀ i : Fin D, ∀ a : A, difference K i • a = 0) (n : ℕ) :
    ((laurentComplex K D).X n ⟶ A) →+ Ext (coefficientModule K D) A n where
  toFun f := (projectiveResolution K D).extMk f (n + 1) rfl
    (boundary_postcomp_zero A hA n f)
  map_zero' := (projectiveResolution K D).extMk_zero (n + 1) rfl
  map_add' f g := ((projectiveResolution K D).add_extMk f g (n + 1) rfl _ _).symm

theorem coefficientMk_surjective (A : ModuleCat (Laurent K D))
    (hA : ∀ i : Fin D, ∀ a : A, difference K i • a = 0) (n : ℕ) :
    Function.Surjective (coefficientMk A hA n) := by
  intro e
  obtain ⟨f, hf, he⟩ := (projectiveResolution K D).extMk_surjective e (n + 1) rfl
  exact ⟨f, he⟩

theorem coefficientMk_injective (A : ModuleCat (Laurent K D))
    (hA : ∀ i : Fin D, ∀ a : A, difference K i • a = 0) (n : ℕ) :
    Function.Injective (coefficientMk A hA n) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  cases n with
  | succ n =>
    obtain ⟨g, hg⟩ := ((projectiveResolution K D).extMk_eq_zero_iff f (n + 2) rfl
      (boundary_postcomp_zero A hA (n + 1) f) n rfl).mp hf
    exact hg.symm.trans (boundary_postcomp_zero A hA n g)
  | zero =>
    change (projectiveResolution K D).extMk f 1 rfl
      (boundary_postcomp_zero A hA 0 f) = 0 at hf
    rw [← (projectiveResolution K D).extEquivCohomologyClass.apply_eq_iff_eq,
      ProjectiveResolution.extEquivCohomologyClass_extMk,
      ProjectiveResolution.extEquivCohomologyClass_zero,
      CohomologyClass.mk_eq_zero_iff] at hf
    obtain ⟨g, hg⟩ := (Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ 1 (by simp)).mp hf
    have hg0 : g = 0 :=
      ((projectiveResolution K D).cochainComplex.isZero_of_isStrictlyLE 0 1).eq_of_src _ _
    rw [hg0, comp_zero] at hg
    have hi := (cancel_epi ((projectiveResolution K D).cochainComplexXIso 0 0 rfl).hom).mp
      (show ((projectiveResolution K D).cochainComplexXIso 0 0 rfl).hom ≫ f =
        ((projectiveResolution K D).cochainComplexXIso 0 0 rfl).hom ≫ 0 by
          simpa using hg.symm)
    exact hi

/-- Lemma 3 for one coefficient source, in every degree including zero:
actual derived Ext is additively isomorphic to all actual cochains. -/
def coefficientExtEquiv (A : ModuleCat (Laurent K D))
    (hA : ∀ i : Fin D, ∀ a : A, difference K i • a = 0) (n : ℕ) :
    Ext (coefficientModule K D) A n ≃+
      ((laurentComplex K D).X n ⟶ A) :=
  (AddEquiv.ofBijective (coefficientMk A hA n)
    ⟨coefficientMk_injective A hA n, coefficientMk_surjective A hA n⟩).symm

@[simp] theorem coefficientExtEquiv_mk (A : ModuleCat (Laurent K D))
    (hA : ∀ i : Fin D, ∀ a : A, difference K i • a = 0) (n : ℕ)
    (f : (laurentComplex K D).X n ⟶ A) :
    coefficientExtEquiv A hA n (coefficientMk A hA n f) = f :=
  (coefficientExtEquiv A hA n).apply_symm_apply f

end
end Decoupling.HighDim.ExtValues
