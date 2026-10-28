import Decoupling.HighDim.KoszulContractionReductionCoordinates
import Decoupling.HighDim.TorusTensorMapsShift

/-!
# The actual augmentation tensor has zero Koszul differentials

This is proved for every component of the literal tensor resolution and
for every integer shift. The final cycle formulas therefore need no
cycle hypothesis from their caller.
-/
namespace Decoupling.HighDim.KoszulContraction
open CategoryTheory CategoryTheory.Limits Koszul TrivialLayers ExtValuesTensor
open scoped TensorProduct ChangeOfRings
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
variable {K : Type} [Field K] {D : ℕ}

def augmentationCoordinate (n : ℕ) (I : Cell D n) :
    (laurentComplex K D).X n ⟶ coefficientModule K D :=
  ModuleCat.ofHom (X := (laurentComplex K D).X n) (Y := coefficientModule K D) {
    toFun v := (show coefficientModule K D from
      (augmentation : Laurent K D →+* K) ((show Term (Laurent K D) D n from v) I))
    map_add' v w := by
      change (augmentation : Laurent K D →+* K)
        ((show Term (Laurent K D) D n from v) I + (show Term (Laurent K D) D n from w) I) = _
      exact map_add _ _ _
    map_smul' r v := by
      change (augmentation : Laurent K D →+* K) (r * (show Term (Laurent K D) D n from v) I) =
        augmentation r * augmentation ((show Term (Laurent K D) D n from v) I)
      exact map_mul _ _ _ }

theorem augmentation_boundary_value (n : ℕ) (v : Term (Laurent K D) D (n + 1))
    (I : Cell D n) : augmentation (boundary (Laurent K D) (difference K) n v I) = 0 := by
  have h := ExtValues.boundary_postcomp_zero (coefficientModule K D)
    (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction _
      augmentationAction_coefficientModule) n (augmentationCoordinate n I)
  have hv := congrArg (fun f : (laurentComplex K D).X (n + 1) ⟶ coefficientModule K D => f v) h
  change augmentation ((show Term (Laurent K D) D n from
    (laurentComplex K D).d (n + 1) n v) I) = 0 at hv
  erw [complex_d] at hv
  exact hv

variable (B : ModuleCat (Laurent K D)) [FiniteDimensional K (Layers.coefficients B)]

theorem reduced_boundary_zero (n : ℕ) :
    (ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).map
      ((tensorComplex B).d (n + 1) n) = 0 := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro z
  apply (reducedTermIso B n).toLinearEquiv.injective
  change (reducedTermIso B n).hom
    ((ModuleCat.extendScalars augmentation).map ((tensorComplex B).d (n + 1) n)
      ((1 : K) ⊗ₜ[Laurent K D,augmentation] z)) = (reducedTermIso B n).hom 0
  rw [map_zero, ModuleCat.ExtendScalars.map_tmul]
  change (reducedTermIso B n).hom
    ((1 : K) ⊗ₜ[Laurent K D,augmentation] ((tensorComplex B).d (n + 1) n z)) = 0
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, TensorProduct.tmul_add, hx, hy, add_zero]
  | tmul v b =>
    rw [tensorComplex_d_tmul]
    funext I
    rw [reducedTermIso_tmul, augmentation_boundary_value, mul_zero, zero_smul]
    rfl

variable (hB : AugmentationAction B)

theorem reduced_cochain_d_zero (p q : ℤ) :
    (ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).map
      ((complex B hB).d p q) = 0 := by
  by_cases hpq : p + 1 = q
  · by_cases hq : q ≤ 0
    · obtain ⟨n, rfl⟩ := Int.exists_eq_neg_ofNat hq
      have hp : p = -((n + 1 : ℕ) : ℤ) := by omega
      subst p
      rw [(resolution B hB).cochainComplex_d _ _ (n + 1) n rfl rfl]
      have hz := reduced_boundary_zero B n
      change (ModuleCat.extendScalars augmentation).map ((resolution B hB).complex.d (n + 1) n) = 0 at hz
      simp only [Functor.map_comp, hz, comp_zero, zero_comp]
    · have hd : (complex B hB).d p q = 0 :=
        ((complex B hB).isZero_of_isStrictlyLE 0 q (by omega)).eq_of_tgt _ _
      rw [hd, Functor.map_zero]
  · rw [(complex B hB).shape p q hpq, Functor.map_zero]

theorem reduced_shift_d_zero (a p q : ℤ) :
    (ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).map
      (((complex B hB)⟦a⟧).d p q) = 0 := by
  rw [CochainComplex.shiftFunctor_obj_d', Functor.map_units_smul, reduced_cochain_d_zero,
    smul_zero]

theorem tensorRestricted_shift_d_zero (a p q : ℤ) :
    (Torus.tensorRestrictedComplex ((complex B hB)⟦a⟧)).d p q = 0 := by
  change (ModuleCat.restrictScalars augmentation).map
    ((ModuleCat.extendScalars augmentation).map (((complex B hB)⟦a⟧).d p q)) = 0
  rw [reduced_shift_d_zero, Functor.map_zero]

theorem tensorRestricted_d_zero (p q : ℤ) :
    (Torus.tensorRestrictedComplex (complex B hB)).d p q = 0 := by
  change (ModuleCat.restrictScalars augmentation).map
    ((ModuleCat.extendScalars augmentation).map ((complex B hB).d p q)) = 0
  rw [reduced_cochain_d_zero, Functor.map_zero]

theorem reduced_doubleShift_d_zero (a b p q : ℤ) :
    (ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).map
      ((((complex B hB)⟦a⟧)⟦b⟧).d p q) = 0 := by
  rw [CochainComplex.shiftFunctor_obj_d', Functor.map_units_smul, reduced_shift_d_zero,
    smul_zero]

theorem tensorRestricted_doubleShift_d_zero (a b p q : ℤ) :
    (Torus.tensorRestrictedComplex (((complex B hB)⟦a⟧)⟦b⟧)).d p q = 0 := by
  change (ModuleCat.restrictScalars augmentation).map
    ((ModuleCat.extendScalars augmentation).map ((((complex B hB)⟦a⟧)⟦b⟧).d p q)) = 0
  rw [reduced_doubleShift_d_zero, Functor.map_zero]

end
end Decoupling.HighDim.KoszulContraction
