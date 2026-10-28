import Decoupling.HighDim.Ext
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.CategoryTheory.Abelian.Projective.Ext
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Positive cohomology of a genuine projective resolution

The complex here consists of the actual linear Hom modules of a mathlib
projective resolution. Its positive homology is identified linearly with
`CategoryTheory.Abelian.Ext`, the Ext defined by the derived category.
In particular, the older derived-functor definition in `Abelian.Ext` is
not silently identified with that Ext. The import supplies `linearYonedaObj`.

This is the cohomology bridge used to define the paper's RHom profile.
Neither finite-dimensionality nor splitting is assumed in this module.
-/

namespace Decoupling.HighDim.ResolutionCohomology

open CategoryTheory CategoryTheory.Abelian

noncomputable section

variable {R : Type} [CommRing R] {X : ModuleCat R}
  (P : ProjectiveResolution X) (Y : ModuleCat R)

/-- The ordinary dual cochain complex of an actual projective resolution. -/
def dualComplex : CochainComplex (ModuleCat R) ℕ :=
  P.complex.linearYonedaObj R Y

@[simp]
theorem dualComplex_d_apply (i j : ℕ) (f : P.complex.X i ⟶ Y) :
    (dualComplex P Y).d i j f = P.complex.d j i ≫ f := rfl

/-- The three terms surrounding the strictly positive degree `n+1`. -/
def positiveSc (n : ℕ) : ShortComplex (ModuleCat R) :=
  (dualComplex P Y).sc' n (n + 1) (n + 2)

theorem extMk_smul (n : ℕ) (a : R) (f : P.complex.X n ⟶ Y)
    (hf : P.complex.d (n + 1) n ≫ f = 0) :
    P.extMk (a • f) (n + 1) rfl (by simp [hf]) =
      a • P.extMk f (n + 1) rfl hf := by
  rw [CategoryTheory.Abelian.Ext.smul_eq_comp_mk₀,
    P.extMk_comp_mk₀]
  simp

/-- Send an actual dual cocycle to its native derived Ext class. -/
def cyclesToExt (n : ℕ) :
    LinearMap.ker (positiveSc P Y n).g.hom →ₗ[R]
      CategoryTheory.Abelian.Ext X Y (n + 1) where
  toFun f := P.extMk f.val (n + 2) (by omega) f.property
  map_add' f g := (P.add_extMk f.val g.val (n + 2) (by omega)
    f.property g.property).symm
  map_smul' a f := extMk_smul P Y (n + 1) a f.val f.property

theorem cyclesToExt_surjective (n : ℕ) : Function.Surjective (cyclesToExt P Y n) := by
  intro α
  obtain ⟨f, hf, hα⟩ := P.extMk_surjective α (n + 2) (by omega)
  exact ⟨⟨f, hf⟩, hα⟩

/-- Vanishing means being a boundary, not merely vanishing in a surrogate quotient. -/
theorem cyclesToExt_ker (n : ℕ) :
    LinearMap.ker (cyclesToExt P Y n) =
      LinearMap.range (positiveSc P Y n).moduleCatToCycles := by
  ext f
  change P.extMk f.val (n + 2) (by omega) f.property = 0 ↔ _
  have h := P.extMk_eq_zero_iff (show P.complex.X (n + 1) ⟶ Y from f.val)
    (n + 2) (by omega) f.property n rfl
  refine h.trans ?_
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, congrArg Subtype.val hg⟩

/-- The explicit quotient of dual cycles by boundaries is genuine Ext. -/
def positiveQuotientEquiv (n : ℕ) :
    (LinearMap.ker (positiveSc P Y n).g.hom ⧸
      LinearMap.range (positiveSc P Y n).moduleCatToCycles) ≃ₗ[R]
        CategoryTheory.Abelian.Ext X Y (n + 1) :=
  (Submodule.quotEquivOfEq _ _ (cyclesToExt_ker P Y n).symm).trans
    ((cyclesToExt P Y n).quotKerEquivOfSurjective (cyclesToExt_surjective P Y n))

/-- Categorical homology of the actual Hom complex is genuine Ext. -/
def positiveHomologyEquiv (n : ℕ) :
    (positiveSc P Y n).homology ≃ₗ[R]
      CategoryTheory.Abelian.Ext X Y (n + 1) :=
  ((positiveSc P Y n).moduleCatHomologyIso.toLinearEquiv).trans
    (positiveQuotientEquiv P Y n)

/-- The same identification for the standard homology functor at `n+1`. -/
def homologyEquivExt (n : ℕ) :
    (dualComplex P Y).homology (n + 1) ≃ₗ[R]
      CategoryTheory.Abelian.Ext X Y (n + 1) :=
  ((dualComplex P Y).homologyIsoSc' n (n + 1) (n + 2)
    (by simp) (by simp)).toLinearEquiv.trans (positiveHomologyEquiv P Y n)

end
end Decoupling.HighDim.ResolutionCohomology
