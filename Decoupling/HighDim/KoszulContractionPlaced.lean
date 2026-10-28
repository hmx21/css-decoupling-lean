import Decoupling.HighDim.KoszulContractionNative
import Decoupling.HighDim.KoszulContractionReduction

/-!
# Actual degree-zero term square for placed contractions

All source and target shifts are retained. This square supplies the
literal component formula used after actual augmentation scalar extension.
-/
namespace Decoupling.HighDim.KoszulContraction
open CategoryTheory CategoryTheory.Limits Koszul TrivialLayers ExtValuesTensor
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {K : Type} [Field K] {D : ℕ}
  (B A : ModuleCat (Laurent K D))
  [FiniteDimensional K (Layers.coefficients B)]
  [FiniteDimensional K (Layers.coefficients A)]
  (hB : AugmentationAction B) (hA : AugmentationAction A)

def placedSourceTermIso (k : ℕ) :
    ((complex B hB)⟦(-(k : ℤ))⟧).X 0 ≅ (tensorComplex B).X k :=
  (complex B hB).shiftFunctorObjXIso (-(k : ℤ)) 0 (-(k : ℤ)) (by omega) ≪≫
    (resolution B hB).cochainComplexXIso (-(k : ℤ)) k rfl

def placedTargetTermIso (n q k : ℕ) (hk : k = q + n) :
    (((complex A hA)⟦(n : ℤ)⟧)⟦(-(k : ℤ))⟧).X 0 ≅ (tensorComplex A).X q :=
  ((complex A hA)⟦(n : ℤ)⟧).shiftFunctorObjXIso (-(k : ℤ)) 0 (-(k : ℤ)) (by omega) ≪≫
    (complex A hA).shiftFunctorObjXIso (n : ℤ) (-(k : ℤ)) (-(q : ℤ)) (by omega) ≪≫
      (resolution A hA).cochainComplexXIso (-(q : ℤ)) q rfl

theorem placed_tableMap_square (n : ℕ)
    (f : Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A))
    (q k : ℕ) (hk : k = q + n) :
    ((tableMap B A hB hA n f)⟦(-(k : ℤ))⟧').f 0 ≫ (placedTargetTermIso A hA n q k hk).hom =
      (placedSourceTermIso B hB k).hom ≫ ((tensorComplex B).XIsoOfEq hk).hom ≫
        tableComponent B A hB n f q := by
  apply (cancel_epi ((complex B hB).shiftFunctorObjXIso (-(k : ℤ)) 0
    (-(k : ℤ)) (by omega)).inv).mp
  simp only [placedSourceTermIso, placedTargetTermIso, Iso.trans_hom, Category.assoc]
  erw [YonedaDetection.shift_component_naturality_assoc
    (tableMap B A hB hA n f) (-(k : ℤ)) 0 (-(k : ℤ)) (by omega)]
  erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc]
  rw [tableMap_f_of_degree B A hB hA n f q k hk]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]

theorem reduced_placed_tableMap_square (n : ℕ)
    (f : Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A))
    (q k : ℕ) (hk : k = q + n) :
    (ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).map
        (((tableMap B A hB hA n f)⟦(-(k : ℤ))⟧').f 0) ≫
      (ModuleCat.extendScalars augmentation).map (placedTargetTermIso A hA n q k hk).hom =
      (ModuleCat.extendScalars augmentation).map (placedSourceTermIso B hB k).hom ≫
        (ModuleCat.extendScalars augmentation).map ((tensorComplex B).XIsoOfEq hk).hom ≫
          (ModuleCat.extendScalars augmentation).map (tableComponent B A hB n f q) := by
  simpa only [Functor.map_comp] using congrArg
    (fun g => (ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).map g)
      (placed_tableMap_square B A hB hA n f q k hk)

end
end Decoupling.HighDim.KoszulContraction
