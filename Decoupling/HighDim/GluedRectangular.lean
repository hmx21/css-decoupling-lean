import Decoupling.HighDim.RectangularLattice
import Decoupling.HighDim.GluedNativeFormality

/-!
# The example's actual obstruction on rectangular periods

The genuine native restricted Ext class vanishes exactly when p divides
the product of the first two periods. The third period is arbitrary.
The proof computes actual Koszul comparison coefficients of the literal
plaquette coupling, retaining its minus sign.
-/

namespace Decoupling.HighDim.Glued

open CategoryTheory CategoryTheory.Abelian Koszul KoszulLattice ExtValues
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

theorem restrictedCoupling_basis (a : Translation 3 →+ Translation 3) (J : Cell 3 2) :
    (show K from (((latticeComparison K a).f 2 ≫
      (ModuleCat.restrictScalars (latticeMap K a)).map (couplingCochain K))
        (Finsupp.single J 1))) =
      -Matrix.det (fun i j => (a (translationBasis (J i)) (plaquette 0 j) : K)) := by
  change (show K from couplingCochain K ((latticeComparison K a).f 2 (Finsupp.single J 1))) = _
  rw [couplingCochain_apply, augmentation_latticeComparison_single]

/-- The three signed 12 minors test the genuine native restriction. -/
theorem couplingRestriction_iff_minor (a : Translation 3 →+ Translation 3) :
    (couplingClass K).mapExactFunctor (ModuleCat.restrictScalars (latticeMap K a)) = 0 ↔
      ∀ J : Cell 3 2,
        Matrix.det (fun i j => (a (translationBasis (J i)) (plaquette 0 j) : K)) = 0 := by
  change (coefficientMk _ _ 2 (couplingCochain K)).mapExactFunctor _ = 0 ↔ _
  rw [coefficient_restriction_eq_zero_iff K a _
    (TrivialLayers.augmentationAction_coefficientModule (K := K) (D := 3))]
  constructor
  · intro h J
    have hh := restrictedCoupling_basis K a J
    rw [h] at hh
    change (0 : K) = -_ at hh
    exact neg_eq_zero.mp hh.symm
  · intro h
    apply ModuleCat.hom_ext
    apply (Finsupp.basisSingleOne : Module.Basis (Cell 3 2) (Laurent K 3)
      (Term (Laurent K 3) 3 2)).ext
    intro J
    change (show K from (((latticeComparison K a).f 2 ≫
      (ModuleCat.restrictScalars (latticeMap K a)).map (couplingCochain K))
        (Finsupp.single J 1))) = 0
    rw [restrictedCoupling_basis, h, neg_zero]

theorem rectangular_minor (L : Fin 3 → ℕ) (j : Fin 3) :
    Matrix.det (fun i k => (RectangularLattice.inclusion L
      (translationBasis (plaquette j i)) (plaquette 0 k) : K)) =
        ![(L 0 : K) * (L 1 : K), 0, 0] j := by
  fin_cases j <;>
    simp [Matrix.det_fin_two, RectangularLattice.inclusion, plaquette, translationBasis]

theorem rectangular_coupling_zero_iff (L : Fin 3 → ℕ) :
    (couplingClass K).mapExactFunctor
      (ModuleCat.restrictScalars (latticeMap K (RectangularLattice.inclusion L))) = 0 ↔
        ((L 0 * L 1 : ℕ) : K) = 0 := by
  rw [couplingRestriction_iff_minor]
  constructor
  · intro h
    simpa only [rectangular_minor, Matrix.cons_val_zero, Nat.cast_mul] using h (plaquette 0)
  · intro h J
    obtain ⟨j, rfl⟩ := plaquette_surjective J
    rw [rectangular_minor]
    fin_cases j
    · simpa [Nat.cast_mul] using h
    · simp
    · simp

/-- Genuine restriction along the actual rectangular inclusion. -/
theorem rectangular_coupling_zero_iff_dvd (p : ℕ) [Fact p.Prime] (L : Fin 3 → ℕ) :
    (couplingClass (ZMod p)).mapExactFunctor
      (ModuleCat.restrictScalars (latticeMap (ZMod p) (RectangularLattice.inclusion L))) = 0 ↔
        p ∣ L 0 * L 1 := by
  rw [rectangular_coupling_zero_iff]
  exact CharP.cast_eq_zero_iff (ZMod p) p (L 0 * L 1)

/-- The actual profile of the displayed code splits on precisely those
rectangular periods with p dividing the first-two-period product. -/
theorem rectangular_profile_formal_iff (p : ℕ) [Fact p.Prime] (L : Fin 3 → ℕ) :
    Nonempty ((ModuleCat.restrictScalars
      (latticeMap (ZMod p) (RectangularLattice.inclusion L))).mapDerivedCategory.obj
        (Profile.S_X (checks (ZMod p))) ≅ twoCoefficientLayers (ZMod p)) ↔
      p ∣ L 0 * L 1 := by
  rw [actualProfile_formal_iff, rectangular_coupling_zero_iff_dvd]

end
end Decoupling.HighDim.Glued
