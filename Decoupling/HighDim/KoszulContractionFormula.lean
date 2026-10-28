import Decoupling.HighDim.KoszulContractionCells

/-!
# Full cell formula for the actual contraction map

HD010 Appendix B.3: the formula concerns components of the genuine
shifted chain map from `KoszulContractionMap`, not a replacement map
defined only on homology.
-/

namespace Decoupling.HighDim.KoszulContraction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open Koszul TrivialLayers ExtValuesTensor CochainComplex.HomComplex Toric.Hodge
open scoped TensorProduct
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type} [Field K] {D : ℕ}
  (B A : ModuleCat (Laurent K D))
  [FiniteDimensional K (Layers.coefficients B)]
  [FiniteDimensional K (Layers.coefficients A)]
  (hB : AugmentationAction B) (hA : AugmentationAction A)

def tableComponent (n : ℕ)
    (f : Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A)) (q : ℕ) :
    (tensorComplex B).X (q + n) ⟶ (tensorComplex A).X q :=
  ∑ I : Cell D n, cellComponent B hB I q ≫ (coefficientChain B A (f I)).f q

theorem cocycle_sum_v {C : Type*} [Category* C] [Preadditive C]
    {X Y : CochainComplex C ℤ} {n : ℤ} {ι : Type*} (s : Finset ι)
    (f : ι → Cocycle X Y n) (p q : ℤ) (hpq : p + n = q) :
    (↑(∑ i ∈ s, f i) : Cochain X Y n).v p q hpq =
      ∑ i ∈ s, (f i : Cochain X Y n).v p q hpq := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp only [Finset.sum_insert hi, Cocycle.coe_add, Cochain.add_v, ih]

theorem tableCocycle_v (n : ℕ)
    (f : Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A)) (q : ℕ) :
    (tableCocycle B A hB hA n f : Cochain (complex B hB) (complex A hA) (n : ℤ)).v
      (-((q + n : ℕ) : ℤ)) (-(q : ℤ)) (by omega) =
      ((resolution B hB).cochainComplexXIso (-((q + n : ℕ) : ℤ)) (q + n) rfl).hom ≫
        tableComponent B A hB n f q ≫
          ((resolution A hA).cochainComplexXIso (-(q : ℤ)) q rfl).inv := by
  rw [tableCocycle, cocycle_sum_v]
  simp only [composeCocycle, Cocycle.mk_coe, Cocycle.ofHom_coe,
    Cochain.comp_zero_cochain_v, Cochain.ofHom_v, tableComponent,
    comp_sum, sum_comp, coefficientMap_f]
  apply Finset.sum_congr rfl
  intro I _
  dsimp only [cellComponent]
  simp only [Category.assoc]
  erw [Iso.hom_inv_id_assoc]

/-- Component formula retaining the actual shift isomorphism and hence
the native sign convention for the target differential. -/
theorem tableMap_f (n : ℕ)
    (f : Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A)) (q : ℕ) :
    (tableMap B A hB hA n f).f (-((q + n : ℕ) : ℤ)) =
      ((resolution B hB).cochainComplexXIso (-((q + n : ℕ) : ℤ)) (q + n) rfl).hom ≫
        tableComponent B A hB n f q ≫
          ((resolution A hA).cochainComplexXIso (-(q : ℤ)) q rfl).inv ≫
            ((complex A hA).shiftFunctorObjXIso (n : ℤ)
              (-((q + n : ℕ) : ℤ)) (-(q : ℤ)) (by omega)).inv := by
  simp only [tableMap, Cocycle.equivHomShift_symm_apply, Cocycle.homOf, Cocycle.rightShift_coe]
  rw [Cochain.rightShift_v _ _ _ _ _ _ _ (-(q : ℤ)) (by omega), tableCocycle_v]
  simp only [Category.assoc]

theorem coefficientChain_deletionValue
    (g : Layers.coefficients B →ₗ[K] Layers.coefficients A)
    (q : ℕ) (r : Option (ℕ × Cell D q)) (b : Layers.coefficients B) :
    (coefficientChain B A g).f q (deletionValue B r b) = deletionValue A r (g b) := by
  cases r with
  | none => exact map_zero _
  | some x => rfl

/-- Every component has the exact signed subcell contraction formula. -/
theorem tableComponent_single (n : ℕ)
    (f : Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A)) (q : ℕ)
    (J : Cell D (q + n)) (b : Layers.coefficients B) :
    tableComponent B A hB n f q (Finsupp.single J 1 ⊗ₜ[K] b) =
      ∑ I : Cell D n, deletionValue A (deletion n I q J) (f I b) := by
  simp only [tableComponent, ModuleCat.hom_sum, LinearMap.sum_apply,
    ModuleCat.hom_comp, LinearMap.comp_apply, cellComponent_single,
    coefficientChain_deletionValue]

/-- The manuscript's subcell sum. The surviving cell is `J \ I`, as
proved by `subcellData_directions`; its sign is the ordered interior
product sign, with no characteristic-two simplification. -/
theorem tableComponent_subcell_formula (n : ℕ)
    (f : Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A)) (q : ℕ)
    (J : Cell D (q + n)) (b : Layers.coefficients B) :
    tableComponent B A hB n f q (Finsupp.single J 1 ⊗ₜ[K] b) =
      ∑ I : Cell D n, if h : directions I ⊆ directions J then
        Finsupp.single (subcellData n I q J h).2
          ((-1 : Laurent K D) ^ (subcellData n I q J h).1) ⊗ₜ[K] f I b else 0 := by
  rw [tableComponent_single]
  apply Finset.sum_congr rfl
  intro I _
  by_cases h : directions I ⊆ directions J
  · rw [deletion_eq_subcellData n I q J h, dite_eq_left h]
    rfl
  · have hn : deletion n I q J = none := by
      by_contra hn
      exact h ((deletion_ne_none_iff n I q J).mp hn)
    rw [hn, dite_eq_right h]
    rfl

end
end Decoupling.HighDim.KoszulContraction
