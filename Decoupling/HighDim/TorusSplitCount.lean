import Decoupling.HighDim.TorusCountBound
import Decoupling.HighDim.TwoLayerMultiplicity

/-!
# Same-lattice decoupling attains the full binomial count

The count is obtained from native morphisms into the genuine toric stack
profile. Its finite biproduct multiplicities are the original Ext ranks.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type} [Field K] {D : ℕ}

/-- The representable functor sends a finite native biproduct to the
actual product of its coefficient-linear morphism spaces. -/
def homBiproductEquiv (P : Derived K D) {ι : Type} [Fintype ι] (X : ι → Derived K D) :
    homCoefficients P (⨁ X) ≃ₗ[K] (∀ i, homCoefficients P (X i)) where
  toFun f i := f ≫ biproduct.π X i
  invFun f := biproduct.lift f
  left_inv f := by
    change biproduct.lift (fun i => (show P ⟶ ⨁ X from f) ≫ biproduct.π X i) = f
    apply biproduct.hom_ext
    intro i
    simp
  right_inv f := by funext i; simp
  map_add' f g := by
    funext i
    change ((show P ⟶ ⨁ X from f) + (show P ⟶ ⨁ X from g)) ≫ biproduct.π X i =
      (show P ⟶ ⨁ X from f) ≫ biproduct.π X i + (show P ⟶ ⨁ X from g) ≫ biproduct.π X i
    simp only [Preadditive.add_comp]
  map_smul' a f := by
    funext i
    change (constant (D := D) a • (show P ⟶ ⨁ X from f)) ≫ biproduct.π X i =
      constant (D := D) a • (f ≫ biproduct.π X i)
    exact CategoryTheory.Linear.smul_comp _ _ _ _ _ _

theorem finrank_hom_biproduct (P : Derived K D) {ι : Type} [Fintype ι]
    (X : ι → Derived K D) [∀ i, Module.Finite K (homCoefficients P (X i))] :
    Module.finrank K (homCoefficients P (⨁ X)) =
      ∑ i, Module.finrank K (homCoefficients P (X i)) := by
  rw [(homBiproductEquiv P X).finrank_eq]
  exact Module.finrank_pi_fintype K

def coefficientModuleCoefficientsIso :
    Layers.coefficients (Koszul.coefficientModule K D) ≅ ModuleCat.of K K :=
  (augmentationCoefficientsIso K D).app (ModuleCat.of K K)

instance coefficientModule_finite :
    Module.Finite K (Layers.coefficients (Koszul.coefficientModule K D)) :=
  Module.Finite.equiv (coefficientModuleCoefficientsIso (K := K) (D := D)).symm.toLinearEquiv

theorem coefficientModule_finrank :
    Module.finrank K (Layers.coefficients (Koszul.coefficientModule K D)) = 1 := by
  exact (coefficientModuleCoefficientsIso (K := K) (D := D)).toLinearEquiv.finrank_eq.trans
    (Module.finrank_self K)

theorem probe_coefficient_finrank (j : ℕ) (hj : 1 ≤ j) (hjD : j < D) :
    Module.finrank K (homCoefficients (probe K D)
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj
        (Koszul.coefficientModule K D))) = D.choose j := by
  have h := (probeSingle_finrank_eq_iff (Koszul.coefficientModule K D) j hj hjD).mpr
    TrivialLayers.augmentationAction_coefficientModule
  simpa only [coefficientModule_finrank, mul_one] using h

theorem finrank_splitTarget {ι : Type} [Fintype ι] (forms : ι → ℕ)
    (hf : ∀ i, forms i + 1 < D) :
    Module.finrank K (homCoefficients (probe K D) (Toric.splitTarget K D forms)) =
      ∑ i, D.choose (forms i + 1) := by
  let : ∀ i, Module.Finite K (homCoefficients (probe K D)
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) (forms i + 1)).obj
        (Koszul.coefficientModule K D))) := fun i =>
    probeSingle_finite (Koszul.coefficientModule K D) (forms i + 1)
      (D - (forms i + 1) - 1) (by have := hf i; omega)
  rw [Toric.splitTarget, finrank_hom_biproduct]
  apply Finset.sum_congr rfl
  intro i _
  exact probe_coefficient_finrank (forms i + 1) (by omega) (hf i)

variable {p q s r : ℕ} [Fact p.Prime]

theorem finrank_multiplicity_splitTarget (c : CSS.Checks (ZMod p) D q s r) :
    Module.finrank (ZMod p) (homCoefficients (probe (ZMod p) D)
      (Toric.splitTarget (ZMod p) D (Toric.copyForms D (SplitMultiplicity.multiplicities c)))) =
        layerBound c := by
  rw [finrank_splitTarget _ (by intro i; have := i.1.isLt; change i.1.val + 1 < D; omega)]
  change (∑ i : Σ j : Fin (D - 1), Fin (SplitMultiplicity.multiplicities c j),
    D.choose (i.1.val + 1)) = _
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    SplitMultiplicity.multiplicities, layerBound, Finset.sum_Ico_eq_sum_range]
  change (∑ i : Fin (D - 1), Layers.multiplicity c (i.val + 1) * D.choose (i.val + 1)) = _
  rw [Fin.sum_univ_eq_sum_range (fun i => Layers.multiplicity c (i + 1) * D.choose (i + 1))]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Nat.add_comm, Nat.mul_comm]

/-- Actual same-lattice stable SUM/SWAP decoupling attains the displayed
number of logical qudits on that same finite torus. -/
theorem maximalCount_of_decouplesOn
    (L : AddSubgroup (Translation D)) [L.FiniteIndex] (e : L ≃+ Translation D)
    (c : CSS.Checks (ZMod p) D q s r) (hc : c.Topological)
    (hd : TwoLayer.DecouplesOn L e c) : logicalQudits L c hc = layerBound c := by
  obtain ⟨f⟩ := (TwoLayer.decouplesOn_iff_nativeSplit L e c hc).mp hd
  let ef := (ScalingLattice.physicalChecksRestrictionIso (ZMod p) L e c).symm ≪≫ f
  rw [logicalQudits_eq_profile L e c hc,
    (homCoefficientsIso (probe (ZMod p) D) ef).toLinearEquiv.finrank_eq]
  exact finrank_multiplicity_splitTarget c

end
end Decoupling.HighDim.Torus
