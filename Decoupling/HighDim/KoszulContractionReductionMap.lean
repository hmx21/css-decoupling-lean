import Decoupling.HighDim.KoszulContractionReduction

/-!
# Explicit subcell formula after genuine scalar extension

The map on the left is `extendScalars augmentation` applied to the
actual contraction component. Its coordinates on actual reduced unit
cells are computed, including every coefficient and interior sign.
-/
namespace Decoupling.HighDim.KoszulContraction
open CategoryTheory Koszul TrivialLayers ExtValuesTensor Toric.Hodge
open scoped TensorProduct ChangeOfRings
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type} [Field K] {D : ℕ}
  (B A : ModuleCat (Laurent K D))
  [FiniteDimensional K (Layers.coefficients B)]
  [FiniteDimensional K (Layers.coefficients A)]
  (hB : AugmentationAction B)

theorem reducedTermIso_signedCell (q s : ℕ) (L : Cell D q) (b : Layers.coefficients A) :
    (reducedTermIso A q).hom
      ((1 : K) ⊗ₜ[Laurent K D,augmentation]
        (Finsupp.single L ((-1 : Laurent K D) ^ s) ⊗ₜ[K] b)) =
      ((-1 : K) ^ s) • Pi.single L b := by
  funext J
  rw [reducedTermIso_tmul]
  by_cases h : L = J
  · subst J
    simp
  · simp [Finsupp.single_eq_of_ne (Ne.symm h), Pi.single_eq_of_ne (Ne.symm h)]

/-- Complete coefficient formula for the genuine scalar-extended map. -/
theorem reduced_tableComponent_formula (n : ℕ)
    (f : Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A)) (q : ℕ)
    (J : Cell D (q + n)) (b : Layers.coefficients B) :
    (reducedTermIso A q).hom
      ((ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).map
        (tableComponent B A hB n f q) (reducedCell B (q + n) J b)) =
      ∑ I : Cell D n, if h : directions I ⊆ directions J then
        ((-1 : K) ^ (subcellData n I q J h).1) •
          Pi.single (subcellData n I q J h).2 (f I b) else 0 := by
  let : Algebra (Laurent K D) K := (augmentation : Laurent K D →+* K).toAlgebra
  rw [reducedCell, ModuleCat.ExtendScalars.map_tmul, tableComponent_subcell_formula,
    TensorProduct.tmul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro I _
  by_cases h : directions I ⊆ directions J
  · simp only [dite_eq_left h]
    exact reducedTermIso_signedCell A q _ _ _
  · simp only [dite_eq_right h, TensorProduct.tmul_zero, map_zero]

end
end Decoupling.HighDim.KoszulContraction
