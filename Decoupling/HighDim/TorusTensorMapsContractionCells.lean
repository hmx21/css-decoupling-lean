import Decoupling.HighDim.TorusTensorMapsContraction
import Decoupling.HighDim.TorusTensorMapsClasses
import Decoupling.HighDim.KoszulContractionPlaced
import Decoupling.HighDim.KoszulContractionReductionMap

/-!
# The actual tensor-induced connecting map on its genuine cell basis

HD010 Appendix B.3. Put i=q+1 and j=q+n, so n=j-i+1.
Both homology bases are proved from actual zero differentials. The map
being evaluated comes from the given derived connecting component δ.
-/
namespace Decoupling.HighDim.Torus.Contraction
open CategoryTheory CategoryTheory.Abelian HomologicalComplex
open Koszul KoszulContraction ExtValuesTensor TrivialLayers Toric.Hodge
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {K : Type} [Field K] {D : ℕ}
  (B A : ModuleCat (Laurent K D))
  [FiniteDimensional K (Layers.coefficients B)] [FiniteDimensional K (Layers.coefficients A)]
  (hB : AugmentationAction B) (hA : AugmentationAction A)

def sourceCellIso (q n : ℕ) :
    ModuleCat.of K (Cell D (q + n) → Layers.coefficients B) ≅
      (sourceModel B hB (q + n)).H0 :=
  (reducedTermIso B (q + n)).symm ≪≫
    ((ModuleCat.extendScalars augmentation).mapIso (placedSourceTermIso B hB (q + n))).symm ≪≫
      tensorClassesFromFieldIso ((complex B hB)⟦(-((q + n : ℕ) : ℤ))⟧)
        (tensorRestricted_shift_d_zero B hB _ _ _) (tensorRestricted_shift_d_zero B hB _ _ _)

def targetCellIso (q n : ℕ) :
    ModuleCat.of K (Cell D q → Layers.coefficients A) ≅
      (targetModel A hA (q + 1) (q + n) n (by omega)).H0 :=
  (reducedTermIso A q).symm ≪≫
    ((ModuleCat.extendScalars augmentation).mapIso (placedTargetTermIso A hA n q (q + n) rfl)).symm ≪≫
      tensorClassesFromFieldIso (((complex A hA)⟦(n : ℤ)⟧)⟦(-((q + n : ℕ) : ℤ))⟧)
        (tensorRestricted_doubleShift_d_zero A hA _ _ _ _) (tensorRestricted_doubleShift_d_zero A hA _ _ _ _)

theorem placed_homology_square (q n : ℕ)
    (f : Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A)) :
    (sourceCellIso B hB q n).hom ≫
        tensorH0Map ((tableMap B A hB hA n f)⟦(-((q + n : ℕ) : ℤ))⟧') ≫
          (targetCellIso A hA q n).inv =
      (reducedTermIso B (q + n)).inv ≫
        (ModuleCat.extendScalars augmentation).map (tableComponent B A hB n f q) ≫
          (reducedTermIso A q).hom := by
  dsimp only [sourceCellIso, targetCellIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv]
  simp only [Category.assoc, tensorClassesFromFieldIso_hom]
  rw [reassoc_of% tensorClassesFromField_naturality
    ((tableMap B A hB hA n f)⟦(-((q + n : ℕ) : ℤ))⟧')
      (tensorRestricted_shift_d_zero B hB _ _ _)
      (tensorRestricted_doubleShift_d_zero A hA _ _ _ _)]
  rw [← tensorClassesFromFieldIso_hom _ (tensorRestricted_doubleShift_d_zero A hA _ _ _ _)]
  simp only [Iso.hom_inv_id_assoc, Functor.mapIso_hom, Functor.mapIso_inv]
  rw [reassoc_of% reduced_placed_tableMap_square B A hB hA n f q (q + n) rfl]
  simp only [← Functor.map_comp_assoc, Category.id_comp,
    HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom, Iso.inv_hom_id_assoc]

theorem source_reducedCell (q n : ℕ) (J : Cell D (q + n)) (b : Layers.coefficients B) :
    (reducedTermIso B (q + n)).inv (Pi.single J b) = reducedCell B (q + n) J b := by
  apply (reducedTermIso B (q + n)).toLinearEquiv.injective
  change ((reducedTermIso B (q + n)).inv ≫ (reducedTermIso B (q + n)).hom) (Pi.single J b) = _
  rw [Iso.inv_hom_id]
  exact (reducedCell_coordinates B (q + n) J b).symm

/-- Explicit signed contraction on actual tensor homology, without any
assumed cycle condition. The output cell is exactly J\I by the proved
`subcellData_directions` theorem. -/
theorem connecting_tensor_cell_formula (q n : ℕ)
    (δ : (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) (q + n)).obj B ⟶
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) (q + 1)).obj A)⟦(1 : ℤ)⟧)
    (J : Cell D (q + n)) (b : Layers.coefficients B) :
    (targetCellIso A hA q n).inv
      (TensorModel.map (sourceModel B hB (q + n))
        (targetModel A hA (q + 1) (q + n) n (by omega)) δ
        ((sourceCellIso B hB q n).hom (Pi.single J b))) =
      ∑ I : Cell D n, if h : directions I ⊆ directions J then
        ((-1 : K) ^ (subcellData n I q J h).1) •
          Pi.single (subcellData n I q J h).2
            ((ExtValues.finiteExtEquiv B A hB hA n
              (TwoLayer.extOfConnecting (q + 1) (q + n) n (by omega) δ)) I b) else 0 := by
  rw [connecting_tensor_map]
  let f := ExtValues.finiteExtEquiv B A hB hA n
    (TwoLayer.extOfConnecting (q + 1) (q + n) n (by omega) δ)
  have hs := congrArg (fun g => g (Pi.single J b)) (placed_homology_square B A hB hA q n f)
  change (targetCellIso A hA q n).inv
    (tensorH0Map ((tableMap B A hB hA n f)⟦(-((q + n : ℕ) : ℤ))⟧')
      ((sourceCellIso B hB q n).hom (Pi.single J b))) =
    (reducedTermIso A q).hom ((ModuleCat.extendScalars augmentation).map (tableComponent B A hB n f q)
      ((reducedTermIso B (q + n)).inv (Pi.single J b))) at hs
  change (targetCellIso A hA q n).inv
    (tensorH0Map ((tableMap B A hB hA n f)⟦(-((q + n : ℕ) : ℤ))⟧')
      ((sourceCellIso B hB q n).hom (Pi.single J b))) = _
  rw [hs, source_reducedCell, reduced_tableComponent_formula]

end
end Decoupling.HighDim.Torus.Contraction
