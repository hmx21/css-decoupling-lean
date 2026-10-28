import Decoupling.HighDim.GluedCoupling
import Decoupling.HighDim.ExtValuesTensorTable
import Decoupling.HighDim.ToricSplitLayers

/-!
# The native Ext class of the displayed coupling

The class is built from the actual signed plaquette-to-vertex coupling
and the genuine Koszul projective resolution. Identification of this
class with the concrete code's profile is supplied in the subsequent
cone comparison, not assumed in this file.
-/

namespace Decoupling.HighDim.Glued

open CategoryTheory CategoryTheory.Abelian Koszul ExtValues Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

/-- The literal augmentation of the displayed -12 coupling. -/
def couplingCochain : ModuleCat.of (Laurent K 3) (Term (Laurent K 3) 3 2) ⟶ coefficientModule K 3 :=
  cellCouplingX K ≫ augmentationMap K 3

theorem coefficient_difference_zero (i : Fin 3) (r : coefficientModule K 3) :
    difference K i • r = 0 := by
  change augmentation (difference K i) * (show K from r) = 0
  simp

/-- A genuine native class, represented by the literal displayed coupling. -/
def couplingClass : Ext (coefficientModule K 3) (coefficientModule K 3) 2 :=
  coefficientMk (coefficientModule K 3) (coefficient_difference_zero K) 2 (couplingCochain K)

theorem couplingCochain_apply (v : Term (Laurent K 3) 3 2) :
    (show K from couplingCochain K v) = -augmentation (v (plaquette 0)) := by
  change augmentation (zeroTermEquiv (Laurent K 3)
    ((coordinates (Laurent K 3) vertexEquiv).symm
      (couplingX K *ᵥ coordinates (Laurent K 3) plaquetteEquiv v))) = _
  have hv : (coordinates (Laurent K 3) vertexEquiv).symm
      (couplingX K *ᵥ coordinates (Laurent K 3) plaquetteEquiv v) =
      Finsupp.single vertex (-v (plaquette 0)) := by
    apply (coordinates (Laurent K 3) vertexEquiv).injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    fin_cases i
    simp [couplingX, Matrix.mulVec, dotProduct, Fin.sum_univ_succ,
      coordinates_apply, vertexEquiv, plaquetteEquiv]
  rw [hv, zeroTermEquiv_single, map_neg]

/-- The ordered native coefficient table is exactly (-1,0,0), over
all characteristics and with the manuscript's plaquette order. -/
theorem couplingClass_table (i : Fin 3) :
    (show K from coefficientTableEquiv (coefficientModule K 3)
      (coefficient_difference_zero K) 2 (couplingClass K) (plaquette i)) =
        ![-1, 0, 0] i := by
  rw [couplingClass, coefficientTableEquiv_mk]
  have he := couplingCochain_apply K (Finsupp.single (plaquette i) 1)
  fin_cases i <;> simp at he ⊢ <;> exact he

theorem couplingClass_ne_zero : couplingClass K ≠ 0 := by
  intro h
  have he := couplingClass_table K 0
  rw [h, map_zero] at he
  change (0 : K) = -1 at he
  exact one_ne_zero (neg_eq_zero.mp he.symm)

/-- The displayed augmentation is an actual cocycle. -/
theorem couplingCochain_boundary :
    boundary (Laurent K 3) (difference K) 2 ≫ couplingCochain K = 0 := by
  simpa only [laurentComplex, complex_d] using
    boundary_postcomp_zero (coefficientModule K 3) (coefficient_difference_zero K) 2
      (couplingCochain K)

end
end Decoupling.HighDim.Glued
