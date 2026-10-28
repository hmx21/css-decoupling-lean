import Decoupling.HighDim.TorusTriangle
import Decoupling.HighDim.TorusLayerEquality
import Decoupling.HighDim.ShiftedExt

/-!
# Native shifted Ext and the torus representable functor

The augmentation module in cohomological degree `D` represents the
Koszul-dual version of torus reduction. This file does not define torus
logical dimension by this representation: that remains the actual
periodic kernel/image quotient. It proves the genuine single-layer
morphism bounds needed for the comparison theorem.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ}

/-- A coefficient-linear refinement of the actual shifted-layer/native-Ext
identification, with the derived shift convention stated explicitly. -/
def singleHomExtEquiv (A B : ModuleCat (Laurent K D)) (a b : ℤ) (n : ℕ)
    (hn : (n : ℤ) + b = a) :
    ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) a).obj A ⟶
      (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) b).obj B) ≃ₗ[Laurent K D]
        Ext A B n := by
  let eA : ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) a).obj A)⟦a⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) 0).obj A :=
    ((DerivedCategory.singleFunctors (ModuleCat (Laurent K D))).shiftIso a 0 a (by simp)).app A
  let eB : ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) b).obj B)⟦a⟧ ≅
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) 0).obj B)⟦(n : ℤ)⟧ :=
    ((DerivedCategory.singleFunctors (ModuleCat (Laurent K D))).shiftIso a (-(n : ℤ)) b
      (by omega)).app B ≪≫
      (((DerivedCategory.singleFunctors (ModuleCat (Laurent K D))).shiftIso
        (n : ℤ) (-(n : ℤ)) 0 (by omega)).app B).symm
  exact (LinearEquiv.ofBijective
    ((shiftFunctor (Derived K D) a).mapLinearMap (Laurent K D))
    ((shiftEquiv (Derived K D) a).fullyFaithfulFunctor.map_bijective _ _)).trans
      ((Linear.homCongr (Laurent K D) eA eB).trans Ext.homLinearEquiv.symm)

/-- Fixed source object for the torus representable functor. -/
def probe (K : Type) [Field K] (D : ℕ) : Derived K D :=
  (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) D).obj (Koszul.coefficientModule K D)

/-- Morphisms from the fixed source to a layer in degree `j` are genuine
Ext in degree `D-j`, with the coefficient vector-space structure. -/
def probeSingleExtEquiv (E : ModuleCat (Laurent K D)) (j n : ℕ)
    (hn : n + j = D) :
    homCoefficients (probe K D)
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj E) ≃ₗ[K]
        Layers.coefficients (ModuleCat.of (Laurent K D)
          (Ext (Koszul.coefficientModule K D) E n)) :=
  by
    let e := singleHomExtEquiv (Koszul.coefficientModule K D) E D j n (by omega)
    exact {
      toFun := e
      invFun := e.symm
      left_inv := e.symm_apply_apply
      right_inv := e.apply_symm_apply
      map_add' := e.map_add
      map_smul' a f := e.map_smul (constant (D := D) a) f }

theorem probeSingle_finite (E : ModuleCat (Laurent K D)) (j n : ℕ)
    (hn : n + 1 + j = D) [Module.Finite K (Layers.coefficients E)] :
    Module.Finite K (homCoefficients (probe K D)
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj E)) :=
  Module.Finite.equiv (probeSingleExtEquiv E j (n + 1) hn).symm

/-- The single-layer binomial bound in the indexing of the manuscript. -/
theorem probeSingle_finrank_le (E : ModuleCat (Laurent K D)) (j : ℕ)
    (hj : j < D) [Module.Finite K (Layers.coefficients E)] :
    Module.finrank K (homCoefficients (probe K D)
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj E)) ≤
        D.choose j * Module.finrank K (Layers.coefficients E) := by
  let n := D - j - 1
  have hn : n + 1 + j = D := by omega
  rw [(probeSingleExtEquiv E j (n + 1) hn).finrank_eq]
  have hchoose : D.choose (n + 1) = D.choose j := by
    have he : n + 1 = D - j := by omega
    rw [he, Nat.choose_symm (by omega : j ≤ D)]
  simpa only [hchoose] using nativeExt_finrank_le E n

/-- Maximal single-layer dimension forces every lattice generator to act
trivially; this is derived, not assumed. -/
theorem probeSingle_finrank_eq_iff (E : ModuleCat (Laurent K D)) (j : ℕ)
    (hj : 1 ≤ j) (hjD : j < D) [Module.Finite K (Layers.coefficients E)] :
    Module.finrank K (homCoefficients (probe K D)
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj E)) =
        D.choose j * Module.finrank K (Layers.coefficients E) ↔
          TrivialLayers.AugmentationAction E := by
  let n := D - j - 1
  have hn : n + 1 + j = D := by omega
  rw [(probeSingleExtEquiv E j (n + 1) hn).finrank_eq]
  have hchoose : D.choose (n + 1) = D.choose j := by
    have he : n + 1 = D - j := by omega
    rw [he, Nat.choose_symm (by omega : j ≤ D)]
  simpa only [hchoose] using nativeExt_finrank_eq_iff E n (by omega)

end
end Decoupling.HighDim.Torus
