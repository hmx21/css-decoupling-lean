import Decoupling.Duality
import Decoupling.ExtCokernel

/-!
# Genuine Ext calculations from injective finite-free presentations

All Ext groups in this file are mathlib's derived-category Ext groups.
The short exact presentation and the dual-coordinate identification are
proved explicitly before using the long exact sequence.

The final computations establish the two rows of Proposition I.3:
`TC₁` has first layer the trivial coefficient module and zero higher layers;
`TC₂` has zero first layer, second layer the trivial coefficient module,
and zero layers above degree two. These are statements about `ExtLayers.E_X`
with the actual conjugated reduced Pauli module as first input.
-/

namespace Decoupling.ToricExt

open Matrix CategoryTheory CategoryTheory.Abelian
open Duality ExtLayers PhysicalKoszul ToricWindows

noncomputable section

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The actual finite-free presentation `Rⁿ → Rᵐ → coker D`. -/
def presentation (D : Matrix m n R) : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk D.mulVecLin (LinearMap.range D.mulVecLin).mkQ (by
    apply LinearMap.ext
    intro a
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩)

omit [Fintype m] [DecidableEq m] [DecidableEq n] in
theorem presentation_shortExact (D : Matrix m n R)
    (hD : Function.Injective (fun a : n → R => D *ᵥ a)) :
    (presentation D).ShortExact where
  exact := by
    apply ((presentation D).moduleCat_exact_iff).mpr
    intro a ha
    exact (Submodule.Quotient.mk_eq_zero _).mp ha
  mono_f := (ModuleCat.mono_iff_injective _).mpr hD
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (LinearMap.range D.mulVecLin).mkQ_surjective

/-- Restriction of functionals becomes multiplication by `Dᵀ` in the dual
standard bases, including its actual image submodule. -/
theorem homRestriction_range_coordinates (D : Matrix m n R) :
    (LinearMap.range (ExtCokernel.homRestriction R (presentation D) (ModuleCat.of R R))).map
        (homCoordinates n).toLinearMap = LinearMap.range D.transpose.mulVecLin := by
  apply Submodule.ext
  intro a
  constructor
  · rintro ⟨f, ⟨g, rfl⟩, hga⟩
    refine ⟨homCoordinates m g, ?_⟩
    exact (homCoordinates_precomp D g).symm.trans hga
  · rintro ⟨a, rfl⟩
    refine ⟨ExtCokernel.homRestriction R (presentation D) (ModuleCat.of R R)
      ((homCoordinates m).symm a), ⟨(homCoordinates m).symm a, rfl⟩, ?_⟩
    change homCoordinates n (ModuleCat.ofHom D.mulVecLin ≫ (homCoordinates m).symm a) = _
    rw [homCoordinates_precomp, LinearEquiv.apply_symm_apply]
    rfl

/-- The cokernel in the genuine Ext¹ long exact sequence is the concrete
matrix cokernel of `Dᵀ`. -/
def homCokernelCoordinates (D : Matrix m n R) :
    ((ModuleCat.of R (n → R) ⟶ ModuleCat.of R R) ⧸
      LinearMap.range (ExtCokernel.homRestriction R (presentation D) (ModuleCat.of R R)))
      ≃ₗ[R] Cokernel D.transpose :=
  Submodule.Quotient.equiv _ _ (homCoordinates n) (homRestriction_range_coordinates D)

instance presentation_projective_left (D : Matrix m n R) : Projective (presentation D).X₁ :=
  ModuleCat.projective_of_free (Pi.basisFun R n)

instance presentation_projective_middle (D : Matrix m n R) : Projective (presentation D).X₂ :=
  ModuleCat.projective_of_free (Pi.basisFun R m)

/-- For an injective finite-free presentation, genuine Ext¹ is the cokernel
of the transpose matrix. -/
def extOneCokerTransposeEquiv (D : Matrix m n R)
    (hD : Function.Injective (fun a : n → R => D *ᵥ a)) :
    Ext (ModuleCat.of R (Cokernel D)) (ModuleCat.of R R) 1 ≃ₗ[R] Cokernel D.transpose :=
  (ExtCokernel.homCokernelEquivExtOne R (presentation_shortExact D hD)
    (ModuleCat.of R R)).symm.trans (homCokernelCoordinates D)

omit [DecidableEq m] [DecidableEq n] in
/-- Both terms of the short resolution are free, so genuine Ext in every
degree at least two vanishes. -/
theorem extHigher_eq_zero (D : Matrix m n R)
    (hD : Function.Injective (fun a : n → R => D *ᵥ a)) (k : ℕ)
    (e : Ext (ModuleCat.of R (Cokernel D)) (ModuleCat.of R R) (k + 2)) : e = 0 := by
  obtain ⟨f, hf⟩ := Ext.contravariant_sequence_exact₃
    (presentation_shortExact D hD) (ModuleCat.of R R) e
    (Ext.eq_zero_of_projective _) (n₀ := k + 1) (by omega)
  rw [Ext.eq_zero_of_projective f, Ext.comp_zero] at hf
  exact hf.symm

/-- For a CSS presentation whose transpose is injective, the first genuine
Ext layer is the syndrome quotient. Conjugation is handled by the proved
quotient equivalence rather than suppressed. -/
def extOneEquivSyndrome {q s r : ℕ} (c : CSS.Checks q s r)
    (h : Function.Injective (fun a : Fin s → R => c.H_X.transpose *ᵥ a)) :
    E_X c 1 ≃ₗ[R] c.N :=
  (extSourceEquiv (conjugateReducedEquiv c).toModuleIso (ModuleCat.of R R) 1).trans
    ((extOneCokerTransposeEquiv c.H_X.transpose h).trans
      (Submodule.quotEquivOfEq _ _ (by rw [Matrix.transpose_transpose])))

/-- An injective transpose presentation has no genuine Ext layers of degree
at least two. -/
theorem higher_layer_eq_zero {q s r : ℕ} (c : CSS.Checks q s r)
    (h : Function.Injective (fun a : Fin s → R => c.H_X.transpose *ᵥ a))
    (k : ℕ) (e : E_X c (k + 2)) : e = 0 := by
  let e' := extSourceEquiv (conjugateReducedEquiv c).toModuleIso
    (ModuleCat.of R R) (k + 2)
  apply e'.injective
  rw [map_zero]
  exact extHigher_eq_zero c.H_X.transpose h k (e' e)

theorem TC₁_transpose_injective :
    Function.Injective (fun a : Fin 1 → R => TC₁.H_X.transpose *ᵥ a) := by
  have h : TC₁.H_X.transpose = partial₃ := by
    funext i j
    fin_cases i <;> fin_cases j <;> rfl
  rw [h]
  exact partial₃_injective

/-- The first entry of the manuscript's toric Ext table, as an equivalence
with the actual trivial coefficient module. -/
def TC₁_E1_equiv : E_X TC₁ 1 ≃ₗ[R] EvaluationLinear.Coefficient :=
  (extOneEquivSyndrome TC₁ TC₁_transpose_injective).trans TC₁_coker_equiv_coefficient

/-- All genuine Ext layers of `TC₁` in degrees at least two vanish. -/
theorem TC₁_higher_eq_zero (k : ℕ) (e : E_X TC₁ (k + 2)) : e = 0 :=
  higher_layer_eq_zero TC₁ TC₁_transpose_injective k e

theorem transpose_partial₂ : partial₂.transpose = partial₂ := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem transpose_partial₃ : partial₃.transpose = partial₁ := by
  funext i j
  fin_cases i
  fin_cases j <;> rfl

/-- The degree-two differential, descended through its actual kernel. -/
def cokerD3ToFree : Cokernel partial₃ →ₗ[R] (Fin 3 → R) :=
  (LinearMap.range partial₃.mulVecLin).liftQ partial₂.mulVecLin (by
    rintro _ ⟨a, rfl⟩
    change partial₂ *ᵥ (partial₃ *ᵥ a) = 0
    rw [mulVec_mulVec, partial₂_mul_partial₃, zero_mulVec])

@[simp] theorem cokerD3ToFree_mk (a : Fin 3 → R) :
    cokerD3ToFree (Submodule.Quotient.mk a) = partial₂ *ᵥ a := rfl

theorem cokerD3ToFree_injective : Function.Injective cokerD3ToFree := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  obtain ⟨v, rfl⟩ := (LinearMap.range partial₃.mulVecLin).mkQ_surjective a
  exact (Submodule.Quotient.mk_eq_zero _).mpr ((exact_partial₂_partial₃ v).mp ha)

theorem idealAugmentation_cokerD3ToFree : idealAugmentation.comp cokerD3ToFree = 0 := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro a
  apply Subtype.ext
  change (partial₁ *ᵥ (partial₂ *ᵥ a)) 0 = 0
  rw [mulVec_mulVec, partial₁_mul_partial₂, zero_mulVec]
  rfl

/-- The actual short exact sequence `0 → coker ∂₃ → R³ → J → 0`. -/
def idealSequence : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk cokerD3ToFree idealAugmentation idealAugmentation_cokerD3ToFree

theorem idealSequence_shortExact : idealSequence.ShortExact where
  exact := by
    apply (idealSequence.moduleCat_exact_iff).mpr
    intro a ha
    have ha' : a ∈ LinearMap.ker idealAugmentation := ha
    rw [ker_idealAugmentation] at ha'
    obtain ⟨b, hb⟩ := ha'
    exact ⟨Submodule.Quotient.mk b, hb⟩
  mono_f := (ModuleCat.mono_iff_injective _).mpr cokerD3ToFree_injective
  epi_g := (ModuleCat.epi_iff_surjective _).mpr idealAugmentation_surjective

instance idealSequence_projective_middle : Projective idealSequence.X₂ :=
  ModuleCat.projective_of_free (Pi.basisFun R (Fin 3))

/-- First Ext of `coker ∂₃`, computed via its length-one free resolution. -/
def cokerD3ExtOneEquivCoefficient :
    Ext (ModuleCat.of R (Cokernel partial₃)) (ModuleCat.of R R) 1 ≃ₗ[R]
      EvaluationLinear.Coefficient :=
  (extOneCokerTransposeEquiv partial₃ partial₃_injective).trans
    ((Submodule.quotEquivOfEq _ _ (by rw [transpose_partial₃]; rfl)).trans
      TC₁_coker_equiv_coefficient)

/-- The actual conjugated reduced module of `TC₂` is the ideal `J`. -/
def TC₂_conjugateReducedEquivJ : conjugate (reduced TC₂) ≃ₗ[R] J :=
  (conjugateReducedEquiv TC₂).trans
    ((Submodule.quotEquivOfEq _ _ (by
      change LinearMap.range partial₂.transpose.mulVecLin = LinearMap.range partial₂.mulVecLin
      rw [transpose_partial₂])).trans TC₂_coker_equiv_J)

/-- The second genuine Ext layer of `TC₂`, obtained by dimension shifting
the actual ideal sequence. -/
def TC₂_E2_equiv : E_X TC₂ 2 ≃ₗ[R] EvaluationLinear.Coefficient :=
  (extSourceEquiv TC₂_conjugateReducedEquivJ.toModuleIso (ModuleCat.of R R) 2).trans
    ((ExtCokernel.dimensionShiftEquiv R idealSequence_shortExact
      (ModuleCat.of R R)).symm.trans cokerD3ExtOneEquivCoefficient)

/-- Every functional on `coker ∂₃` extends across its inclusion into `R³`.
The extension is obtained from the proved dual Koszul exactness. -/
theorem idealHomRestriction_surjective :
    Function.Surjective
      (ExtCokernel.homRestriction R idealSequence (ModuleCat.of R R)) := by
  intro f
  let q := (LinearMap.range partial₃.mulVecLin).mkQ
  let f' : Cokernel partial₃ →ₗ[R] R := f.hom
  let g : (Fin 3 → R) →ₗ[R] R := f'.comp q
  have hg : g.comp partial₃.mulVecLin = 0 := by
    apply LinearMap.ext
    intro a
    change f' (Submodule.Quotient.mk (partial₃ *ᵥ a)) = 0
    have ha : (Submodule.Quotient.mk (partial₃ *ᵥ a) : Cokernel partial₃) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩
    rw [ha, map_zero]
  have hcycle : partial₁ *ᵥ dualCoordinates (Fin 3) g = 0 := by
    rw [← transpose_partial₃, ← dualCoordinates_precomp, hg, map_zero]
  obtain ⟨b, hb⟩ := (exact_partial₁_partial₂ _).mp hcycle
  let h : (Fin 3 → R) →ₗ[R] R := (dualCoordinates (Fin 3)).symm b
  have hh : h.comp partial₂.mulVecLin = g := by
    apply (dualCoordinates (Fin 3)).injective
    rw [dualCoordinates_precomp, transpose_partial₂]
    simpa only [h, LinearEquiv.apply_symm_apply] using hb
  refine ⟨ModuleCat.ofHom h, ?_⟩
  apply ModuleCat.hom_ext
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro a
  exact DFunLike.congr_fun hh a

/-- The first genuine Ext group of the actual ideal `J` vanishes. -/
theorem idealExtOne_eq_zero (e : Ext (ModuleCat.of R J) (ModuleCat.of R R) 1) : e = 0 := by
  obtain ⟨f, rfl⟩ := ExtCokernel.connectingHom_surjective R idealSequence_shortExact
    (ModuleCat.of R R) e
  obtain ⟨g, rfl⟩ := idealHomRestriction_surjective f
  have hm : ExtCokernel.homRestriction R idealSequence (ModuleCat.of R R) g ∈
      LinearMap.ker (ExtCokernel.connectingHom R idealSequence_shortExact (ModuleCat.of R R)) := by
    rw [← ExtCokernel.range_homRestriction R idealSequence_shortExact (ModuleCat.of R R)]
    exact ⟨g, rfl⟩
  exact hm

/-- The first genuine Ext layer of the second toric window is zero. -/
theorem TC₂_E1_eq_zero (e : E_X TC₂ 1) : e = 0 := by
  let e' := extSourceEquiv TC₂_conjugateReducedEquivJ.toModuleIso (ModuleCat.of R R) 1
  apply e'.injective
  rw [map_zero]
  exact idealExtOne_eq_zero (e' e)

/-- The ideal sequence and the length-one resolution of `coker ∂₃` also
give vanishing in all degrees above the table's nonzero second layer. -/
theorem idealExtHigher_eq_zero (k : ℕ)
    (e : Ext (ModuleCat.of R J) (ModuleCat.of R R) (k + 3)) : e = 0 := by
  obtain ⟨f, hf⟩ := Ext.contravariant_sequence_exact₃ idealSequence_shortExact
    (ModuleCat.of R R) e (Ext.eq_zero_of_projective _) (n₀ := k + 2) (by omega)
  have hfzero : f = 0 := extHigher_eq_zero partial₃ partial₃_injective k f
  rw [hfzero, Ext.comp_zero] at hf
  exact hf.symm

theorem TC₂_higher_eq_zero (k : ℕ) (e : E_X TC₂ (k + 3)) : e = 0 := by
  let e' := extSourceEquiv TC₂_conjugateReducedEquivJ.toModuleIso (ModuleCat.of R R) (k + 3)
  apply e'.injective
  rw [map_zero]
  exact idealExtHigher_eq_zero k (e' e)

end

end Decoupling.ToricExt
