import Decoupling.HighDim.Ext
import Decoupling.HighDim.RingDimension
import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# The degree bound from the topological condition (Lemma 3)

Source: `drafts/appendix.tex` 6–27. The actual reduced Pauli module
embeds in the Z-check free module, so dimension shifting improves the
Laurent ring's global bound by one. Conjugation is transported through its
actual equivalence of module categories. Neither Ext vanishing nor a free
resolution is an extra input. The result applies over every field.
-/

namespace Decoupling.HighDim.DegreeBound

open CategoryTheory CategoryTheory.Abelian
noncomputable section

variable {K : Type} [Field K] {D q s r : ℕ}
variable (c : CSS.Checks K D q s r) (hc : c.Topological)

def embeddedSequence : ShortComplex (ModuleCat (Laurent K D)) :=
  ShortComplex.moduleCatMk (c.reducedEmbedding hc) (LinearMap.range c.H_Z.mulVecLin).mkQ (by
    apply LinearMap.ext
    intro a
    exact (Submodule.Quotient.mk_eq_zero _).mpr ((c.reducedEquivRange hc) a).property)

theorem embeddedSequence_shortExact : (embeddedSequence c hc).ShortExact where
  exact := by
    apply ((embeddedSequence c hc).moduleCat_exact_iff).mpr
    intro a ha
    let a' : LinearMap.range c.H_Z.mulVecLin :=
      ⟨a, (Submodule.Quotient.mk_eq_zero _).mp ha⟩
    refine ⟨(c.reducedEquivRange hc).symm a', ?_⟩
    exact congrArg Subtype.val ((c.reducedEquivRange hc).apply_symm_apply a')
  mono_f := (ModuleCat.mono_iff_injective _).mpr (c.reducedEmbedding_injective hc)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr
    (LinearMap.range c.H_Z.mulVecLin).mkQ_surjective

instance embeddedSequence_projective_middle : Projective (embeddedSequence c hc).X₂ :=
  ModuleCat.projective_of_free (Pi.basisFun (Laurent K D) (Fin r))

include hc

theorem reduced_projectiveDimensionLE (hD : 1 ≤ D) :
    HasProjectiveDimensionLE (Layers.reduced c) (D - 1) := by
  have hQ : HasProjectiveDimensionLT (embeddedSequence c hc).X₃ ((D - 1) + 2) := by
    have h := RingDimension.projectiveDimensionLE K D (embeddedSequence c hc).X₃
    have he : (D - 1) + 2 = D + 1 := by omega
    simpa only [he] using h
  exact ((embeddedSequence_shortExact c hc).hasProjectiveDimensionLT_X₃_iff
    (D - 1) inferInstance).mp hQ

theorem conjugate_projectiveDimensionLE (hD : 1 ≤ D) :
    HasProjectiveDimensionLE (Layers.conjugate (Layers.reduced c)) (D - 1) := by
  have : HasProjectiveDimensionLE (Layers.reduced c) (D - 1) :=
    reduced_projectiveDimensionLE c hc hD
  exact ScalarExtensionDimension.functor_projectiveDimensionLE
    (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
      (bar : Laurent K D ≃+* Laurent K D)).functor (D - 1) (Layers.reduced c)

/-- Lemma 3, on the actual derived Ext and with the conjugate module retained. -/
theorem ext_eq_zero (hD : 1 ≤ D) {j : ℕ} (hj : D ≤ j) (e : Layers.E_X c j) : e = 0 := by
  have : HasProjectiveDimensionLT (Layers.conjugate (Layers.reduced c)) D := by
    have h := conjugate_projectiveDimensionLE c hc hD
    have he : D - 1 + 1 = D := Nat.sub_add_cancel hD
    simpa only [HasProjectiveDimensionLE, he] using h
  exact e.eq_zero_of_hasProjectiveDimensionLT D hj

theorem ext_subsingleton (hD : 1 ≤ D) {j : ℕ} (hj : D ≤ j) :
    Subsingleton (Layers.E_X c j) :=
  ⟨fun a b => (ext_eq_zero c hc hD hj a).trans (ext_eq_zero c hc hD hj b).symm⟩

/-- The same conclusion for the other entire sector. -/
theorem z_ext_eq_zero (hD : 1 ≤ D) {j : ℕ} (hj : D ≤ j) (e : Layers.E_Z c j) : e = 0 :=
  ext_eq_zero c.swap (c.topological_swap hc) hD hj e

end
end Decoupling.HighDim.DegreeBound
