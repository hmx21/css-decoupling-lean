import Decoupling.HighDim.Ext
import Decoupling.HighDim.KoszulScaledComparison
import Decoupling.HighDim.KoszulExtendFunctor

/-!
# Vanishing of native positive Ext under one p-scaling step

The comparison below is the actual semilinear diagonal Koszul map, extended
to integer cochain degrees and proved a quasi-isomorphism. Its compatibility
with `Ext.mapExactFunctor` uses the native projective-resolution constructor
and the actual derived localization; it is not a surrogate Ext group.
-/

namespace Decoupling.HighDim.Koszul

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [CommRing K] [IsDomain K] (D p : ℕ)
  [Fact p.Prime] [CharP K p]

/-- The native cochain comparison used by actual derived Ext restriction. -/
def scalingCochainComparison : (projectiveResolution K D).cochainComplex ⟶
    ((ModuleCat.restrictScalars (scaling K D p)).mapHomologicalComplex (.up ℤ)).obj
      (projectiveResolution K D).cochainComplex :=
  HomologicalComplex.extendMap (scalingComparison K D p) ComplexShape.embeddingDownNat ≫
    (KoszulExtendFunctor.iso (ModuleCat.restrictScalars (scaling K D p))
      (laurentComplex K D)).inv

instance scalingCochainComparison_quasiIso : QuasiIso (scalingCochainComparison K D p) := by
  dsimp [scalingCochainComparison]
  infer_instance

theorem scalingCochainComparison_f (n : ℕ) :
    (scalingCochainComparison K D p).f (-(n : ℤ)) =
      ((projectiveResolution K D).cochainComplexXIso (-n) n rfl).hom ≫
      (scalingComparison K D p).f n ≫
      (ModuleCat.restrictScalars (scaling K D p)).map
        ((projectiveResolution K D).cochainComplexXIso (-n) n rfl).inv := by
  change (HomologicalComplex.extendMap (scalingComparison K D p) ComplexShape.embeddingDownNat ≫
    (KoszulExtendFunctor.iso (ModuleCat.restrictScalars (scaling K D p))
      (laurentComplex K D)).inv).f (-(n : ℤ)) = _
  simp only [HomologicalComplex.comp_f]
  rw [HomologicalComplex.extendMap_f _ _ (i := n) (i' := -(n : ℤ)) rfl]
  simp only [KoszulExtendFunctor.iso, HomologicalComplex.Hom.isoOfComponents_inv_f,
    KoszulExtendFunctor.termIso_nat, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  rfl

/-- One p-scaling step kills every positive native Ext class from the
coefficient module to any augmentation-annihilated module. -/
theorem coefficient_ext_restriction_eq_zero (B : ModuleCat (Laurent K D))
    (hB : ∀ i : Fin D, ∀ b : B, difference K i • b = 0)
    (n : ℕ) (e : Ext (coefficientModule K D) B (n + 1)) :
    e.mapExactFunctor (ModuleCat.restrictScalars (scaling K D p)) = 0 := by
  obtain ⟨f, hf, rfl⟩ := (projectiveResolution K D).extMk_surjective e (n + 2) (by omega)
  apply KoszulExtFunctor.map_extMk_eq_zero_of_component
    (ModuleCat.restrictScalars (scaling K D p)) (projectiveResolution K D) f hf
    (scalingCochainComparison K D p)
  rw [scalingCochainComparison_f, Functor.map_comp]
  simp only [Category.assoc, ← Functor.map_comp, Iso.inv_hom_id_assoc]
  rw [scalingComparison_postcomp_zero K D p B hB n f, comp_zero]

end
end Decoupling.HighDim.Koszul
