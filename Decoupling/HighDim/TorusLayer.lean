import Decoupling.HighDim.TorusHomology
import Decoupling.HighDim.TorusCells
import Decoupling.HighDim.KoszulResolution
import Decoupling.HighDim.ResolutionCohomology
import Decoupling.HighDim.TrivialLayers

/-!
# The native Koszul Ext bound for an arbitrary finite layer

Source: Appendix B.3. This module computes the actual native Ext from the
augmentation module to an arbitrary Laurent module. No trivial translation
action is assumed in its dimension bound. Koszul self-duality will identify
this group in degree `D-j` with the dual-index torus contribution.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Abelian Koszul ResolutionCohomology
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ} (E : ModuleCat (Laurent K D))

/-- Coefficient-field coordinates on actual resolution-to-module morphisms. -/
def homValues (k : ℕ) :
    Layers.coefficients (ModuleCat.of (Laurent K D)
      ((laurentComplex K D).X k ⟶ E)) ≃ₗ[K] (Cell D k → Layers.coefficients E) where
  toFun f I := (show (laurentComplex K D).X k ⟶ E from f) (Finsupp.single I 1)
  invFun v := ModuleCat.ofHom (Finsupp.linearCombination (Laurent K D) (fun I => (show E from v I)))
  left_inv f := by
    apply ModuleCat.hom_ext
    apply Finsupp.lhom_ext
    intro I a
    simp only [ModuleCat.hom_ofHom, Finsupp.linearCombination_single]
    change a • (show (laurentComplex K D).X k ⟶ E from f) (Finsupp.single I 1) =
      (show (laurentComplex K D).X k ⟶ E from f) (Finsupp.single I a)
    have hs : a • (Finsupp.single I 1 : Term (Laurent K D) D k) = Finsupp.single I a := by
      simp
    rw [← hs]
    exact ((show (laurentComplex K D).X k ⟶ E from f).hom.map_smul a (Finsupp.single I 1)).symm
  right_inv v := by
    funext I
    change (Finsupp.linearCombination (Laurent K D) (fun I => (show E from v I))) (Finsupp.single I 1) = v I
    rw [Finsupp.linearCombination_single, one_smul]
  map_add' f g := by
    funext I
    rfl
  map_smul' a f := by
    funext I
    rfl

/-- Native Koszul Hom short complex with scalar restriction only. -/
def layerSc (n : ℕ) : ShortComplex (ModuleCat K) :=
  (positiveSc (projectiveResolution K D) E n).map (ModuleCat.restrictScalars constant)

@[simp] theorem layerSc_f_apply (n : ℕ) (f : (laurentComplex K D).X n ⟶ E) :
    (layerSc E n).f f = boundary (Laurent K D) (difference K) n ≫ f := by
  change (laurentComplex K D).d (n + 1) n ≫ f = _
  simp only [laurentComplex, complex_d]

@[simp] theorem layerSc_g_apply (n : ℕ) (f : (laurentComplex K D).X (n + 1) ⟶ E) :
    (layerSc E n).g f = boundary (Laurent K D) (difference K) (n + 1) ≫ f := by
  change (laurentComplex K D).d (n + 2) (n + 1) ≫ f = _
  simp only [laurentComplex, complex_d]

instance layerSc_finite (n : ℕ) [Module.Finite K (Layers.coefficients E)] :
    Module.Finite K (layerSc E n).X₂ :=
  Module.Finite.equiv (homValues E (n + 1)).symm

/-- Restriction to the coefficient field preserves genuine homology. -/
def layerHomologyEquivExt (n : ℕ) :
    (layerSc E n).homology ≃ₗ[K]
      Layers.coefficients (ModuleCat.of (Laurent K D)
        (Ext (coefficientModule K D) E (n + 1))) :=
  ((positiveSc (projectiveResolution K D) E n).mapHomologyIso
    (ModuleCat.restrictScalars constant)).toLinearEquiv.trans
      (((ModuleCat.restrictScalars constant).mapIso
        (positiveHomologyEquiv (projectiveResolution K D) E n).toModuleIso).toLinearEquiv)

instance coefficientExt_finite (n : ℕ) [Module.Finite K (Layers.coefficients E)] :
    Module.Finite K (Layers.coefficients (ModuleCat.of (Laurent K D)
      (Ext (coefficientModule K D) E (n + 1)))) :=
  Module.Finite.equiv (layerHomologyEquivExt E n)

/-- Term rank is binomial coefficient times actual layer dimension. -/
theorem layerSc_finrank (n : ℕ) [Module.Finite K (Layers.coefficients E)] :
    Module.finrank K (layerSc E n).X₂ =
      D.choose (n + 1) * Module.finrank K (Layers.coefficients E) := by
  change Module.finrank K (Layers.coefficients (ModuleCat.of (Laurent K D)
    ((laurentComplex K D).X (n + 1) ⟶ E))) = _
  rw [(homValues E (n + 1)).finrank_eq]
  rw [Module.finrank_pi_fintype]
  simp

/-- The upper bound does not require trivial layer action. -/
theorem nativeExt_finrank_le (n : ℕ) [Module.Finite K (Layers.coefficients E)] :
    Module.finrank K (Layers.coefficients (ModuleCat.of (Laurent K D)
      (Ext (coefficientModule K D) E (n + 1)))) ≤
      D.choose (n + 1) * Module.finrank K (Layers.coefficients E) := by
  rw [← (layerHomologyEquivExt E n).finrank_eq, ← layerSc_finrank E n]
  exact finrank_homology_le _

end
end Decoupling.HighDim.Torus
