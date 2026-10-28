import Decoupling.HighDim.TorusLayer
import Decoupling.HighDim.ExtRestrictionVanishing

/-!
# Equality in the native layer bound detects trivial translation action

Source: Appendix B.3. No action hypothesis is used in the necessity proof:
a nonzero coordinate difference is isolated in an actual Koszul
coboundary, using distinct signed faces.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Abelian Koszul ResolutionCohomology
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ} (E : ModuleCat (Laurent K D))

/-- A homomorphism supported on one actual ordered cell. -/
def cellEvaluation {k : ℕ} (I : Cell D k) (b : E) :
    (laurentComplex K D).X k ⟶ E :=
  ModuleCat.ofHom ((Finsupp.lapply I).smulRight b)

@[simp] theorem cellEvaluation_apply {k : ℕ} (I : Cell D k) (b : E)
    (v : Term (Laurent K D) D k) : cellEvaluation E I b v = v I • b := rfl

/-- A single nontrivial translation produces a nonzero actual outgoing
Koszul Hom differential in every degree below `D`. -/
theorem layerSc_g_ne_zero (n : ℕ) (hn : n + 1 < D) (a : Fin D) (b : E)
    (hb : difference K a • b ≠ 0) : (layerSc E n).g ≠ 0 := by
  intro hz
  obtain ⟨I, i, hi⟩ := exists_cell_containing (by omega : 1 ≤ n + 2)
    (by omega : n + 2 ≤ D) a
  have h := congrArg
    (fun g : (layerSc E n).X₂ ⟶ (layerSc E n).X₃ =>
      (show (laurentComplex K D).X (n + 2) ⟶ E from
        g (cellEvaluation E (face I i) b)) (Finsupp.single I 1)) hz
  rw [layerSc_g_apply] at h
  change cellEvaluation E (face I i) b
      (boundary (Laurent K D) (difference K) (n + 1) (Finsupp.single I 1)) = 0 at h
  rw [cellEvaluation_apply, boundary_coefficient, mul_smul, hi] at h
  exact hb ((isUnit_neg_one.pow i.val).smul_eq_zero.mp h)

/-- Coordinate differences annihilate the module precisely when the
full Laurent action is augmentation. Negative translations are included
through the already proved augmentation-ideal identity. -/
theorem augmentationAction_iff_differences : TrivialLayers.AugmentationAction E ↔
    ∀ (a : Fin D) (b : E), difference K a • b = 0 := by
  constructor
  · exact ExtRestrictionVanishing.difference_annihilates_of_augmentationAction E
  · intro h
    apply ExtRestrictionVanishing.augmentationAction_of_ideal_annihilates E
    intro r hr
    induction hr using Submodule.span_induction with
    | mem r hr =>
      obtain ⟨a, rfl⟩ := hr
      exact h a
    | zero => intro b; simp
    | add r s hr hs ihr ihs => intro b; simp [add_smul, ihr, ihs]
    | smul r s hs ih => intro b; simp [smul_eq_mul, mul_smul, ih]

/-- Augmentation action makes all actual Hom differentials zero. -/
theorem dual_boundary_zero_of_augmentation (hE : TrivialLayers.AugmentationAction E)
    (k : ℕ) (f : (laurentComplex K D).X k ⟶ E) :
    boundary (Laurent K D) (difference K) k ≫ f = 0 := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro I a
  change f (boundary (Laurent K D) (difference K) k (Finsupp.single I a)) = 0
  have hs : (Finsupp.single I a : Term (Laurent K D) D (k + 1)) =
      a • Finsupp.single I 1 := by simp
  rw [hs, map_smul, map_smul]
  suffices h : f (boundary (Laurent K D) (difference K) k (Finsupp.single I 1)) = 0 by
    rw [h, smul_zero]
  rw [boundary_basis, map_sum]
  apply Finset.sum_eq_zero
  intro i _
  have hsingle : (Finsupp.single (face I i) ((-1 : Laurent K D) ^ i.val * difference K (I i)) :
      Term (Laurent K D) D k) =
      ((-1 : Laurent K D) ^ i.val * difference K (I i)) • Finsupp.single (face I i) 1 := by simp
  rw [hsingle, map_smul, mul_smul]
  rw [(augmentationAction_iff_differences E).mp hE, smul_zero]

/-- Equality in an interior native Ext bound is equivalent to trivial
translation action on the original finite layer. -/
theorem nativeExt_finrank_eq_iff (n : ℕ) (hn : n + 1 < D)
    [Module.Finite K (Layers.coefficients E)] :
    Module.finrank K (Layers.coefficients (ModuleCat.of (Laurent K D)
      (Ext (coefficientModule K D) E (n + 1)))) =
      D.choose (n + 1) * Module.finrank K (Layers.coefficients E) ↔
        TrivialLayers.AugmentationAction E := by
  rw [← (layerHomologyEquivExt E n).finrank_eq, ← layerSc_finrank E n,
    finrank_homology_eq_iff]
  constructor
  · rintro ⟨_, hg⟩
    rw [augmentationAction_iff_differences]
    intro a b
    by_contra hb
    exact layerSc_g_ne_zero E n hn a b hb hg
  · intro hE
    constructor
    · ext f
      change (layerSc E n).f f = 0
      rw [layerSc_f_apply]
      exact dual_boundary_zero_of_augmentation E hE n f
    · ext f
      change (layerSc E n).g f = 0
      rw [layerSc_g_apply]
      exact dual_boundary_zero_of_augmentation E hE (n + 1) f

end
end Decoupling.HighDim.Torus
