import Decoupling.HighDim.KoszulContractionNative
import Decoupling.HighDim.KoszulContractionBounds
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Actual augmentation-tensor cell coordinates

The source of the equivalence is the genuine scalar extension
`K ⊗[R] (K_q ⊗[K] B)`. Evaluation on a pure tensor is proved; no
homology or replacement vector space is introduced by definition.
-/
namespace Decoupling.HighDim.KoszulContraction
open CategoryTheory Koszul TrivialLayers ExtValuesTensor
open scoped TensorProduct ChangeOfRings
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type} [Field K] {D : ℕ}
  (B : ModuleCat (Laurent K D)) [FiniteDimensional K (Layers.coefficients B)]

abbrev CoordinateIndex (n : ℕ) := Fin (Module.finrank K (Layers.coefficients B)) × Cell D n

def tensorFreeCoordinates (n : ℕ) :
    TensorTerm B n ≃ₗ[Laurent K D] (CoordinateIndex B n → Laurent K D) where
  toFun z i := tensorTermEquiv B n z i.1 i.2
  invFun w := (tensorTermEquiv B n).symm (fun i =>
    (Finsupp.linearEquivFunOnFinite (Laurent K D) (Laurent K D) (Cell D n)).symm
      (fun J => w (i, J)))
  left_inv z := by
    apply (tensorTermEquiv B n).injective
    simp
  right_inv w := by
    funext i
    simp
  map_add' x y := by
    funext i
    simp
  map_smul' r z := by
    funext i
    simp

theorem tensorFreeCoordinates_tmul (n : ℕ) (v : Term (Laurent K D) D n)
    (b : Layers.coefficients B) (i : CoordinateIndex B n) :
    tensorFreeCoordinates B n (v ⊗ₜ[K] b) i =
      constant ((Module.finBasis K (Layers.coefficients B)).repr b i.1) * v i.2 := by
  change tensorTermEquiv B n (v ⊗ₜ[K] b) i.1 i.2 = _
  rw [tensorTermEquiv_tmul]
  change (Module.finBasis K (Layers.coefficients B)).repr b i.1 • v i.2 = _
  exact Algebra.smul_def _ _

def coefficientCellCoordinates (n : ℕ) :
    (CoordinateIndex B n → K) ≃ₗ[K] (Cell D n → Layers.coefficients B) where
  toFun w J := (Module.finBasis K (Layers.coefficients B)).equivFun.symm (fun i => w (i, J))
  invFun v i := (Module.finBasis K (Layers.coefficients B)).equivFun (v i.2) i.1
  left_inv w := by
    funext i
    change (Module.finBasis K (Layers.coefficients B)).equivFun
      ((Module.finBasis K (Layers.coefficients B)).equivFun.symm (fun a => w (a, i.2))) i.1 = w i
    rw [LinearEquiv.apply_symm_apply]
  right_inv v := by funext J; simp
  map_add' w z := by funext J; exact (Module.finBasis K (Layers.coefficients B)).equivFun.symm.map_add _ _
  map_smul' a w := by funext J; exact (Module.finBasis K (Layers.coefficients B)).equivFun.symm.map_smul a _

def tensorFreeIso (n : ℕ) : (tensorComplex B).X n ≅
    ModuleCat.of (Laurent K D) (CoordinateIndex B n → Laurent K D) :=
  (tensorFreeCoordinates B n).toModuleIso

/-- The actual scalar-extended term is the finite table of coefficients. -/
def reducedTermIso (n : ℕ) :
    (ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).obj ((tensorComplex B).X n) ≅
      ModuleCat.of K (Cell D n → Layers.coefficients B) := by
  letI : Algebra (Laurent K D) K := (augmentation : Laurent K D →+* K).toAlgebra
  exact (ModuleCat.extendScalars augmentation).mapIso (tensorFreeIso B n) ≪≫
    (TensorProduct.piScalarRight (Laurent K D) K K (CoordinateIndex B n)).toModuleIso ≪≫
      (coefficientCellCoordinates B n).toModuleIso

/-- Evaluation formula for the genuine nested tensor product. -/
theorem reducedTermIso_tmul (n : ℕ) (a : K) (v : Term (Laurent K D) D n)
    (b : Layers.coefficients B) (J : Cell D n) :
    (reducedTermIso B n).hom (a ⊗ₜ[Laurent K D,augmentation] (v ⊗ₜ[K] b)) J =
      (a * augmentation (v J)) • b := by
  let : Algebra (Laurent K D) K := (augmentation : Laurent K D →+* K).toAlgebra
  apply (Module.finBasis K (Layers.coefficients B)).equivFun.injective
  funext i
  change (Module.finBasis K (Layers.coefficients B)).equivFun
    ((coefficientCellCoordinates B n)
      (TensorProduct.piScalarRight (Laurent K D) K K (CoordinateIndex B n)
        ((ModuleCat.extendScalars augmentation).map (tensorFreeIso B n).hom
          (a ⊗ₜ[Laurent K D] (v ⊗ₜ[K] b)))) J) i = _
  rw [ModuleCat.ExtendScalars.map_tmul, TensorProduct.piScalarRight_apply,
    TensorProduct.piScalarRightHom_tmul]
  change (Module.finBasis K (Layers.coefficients B)).equivFun
    ((Module.finBasis K (Layers.coefficients B)).equivFun.symm
      (fun i => augmentation (tensorFreeCoordinates B n (v ⊗ₜ[K] b) (i, J)) * a)) i = _
  rw [LinearEquiv.apply_symm_apply, tensorFreeCoordinates_tmul, map_mul, augmentation_constant]
  simp only [map_smul, Pi.smul_apply, smul_eq_mul, Module.Basis.equivFun_apply]
  ring

def reducedCell (n : ℕ) (I : Cell D n) (b : Layers.coefficients B) :
    (ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).obj ((tensorComplex B).X n) :=
  (1 : K) ⊗ₜ[Laurent K D,augmentation] (Finsupp.single I 1 ⊗ₜ[K] b)

theorem reducedCell_coordinates (n : ℕ) (I : Cell D n) (b : Layers.coefficients B) :
    (reducedTermIso B n).hom (reducedCell B n I b) = Pi.single I b := by
  classical
  funext J
  rw [reducedCell, reducedTermIso_tmul]
  by_cases h : I = J
  · subst J
    simp
  · simp [Finsupp.single_eq_of_ne (Ne.symm h), Pi.single_eq_of_ne (Ne.symm h)]

end
end Decoupling.HighDim.KoszulContraction
