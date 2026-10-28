import Decoupling.HighDim.ToricGauge
import Decoupling.HighDim.ToricHodgeCoordinates

/-!
# Actual dual-lattice Hodge map with the required monomial translations

The map on a cell is its complementary dual cell multiplied by the
explicit orientation sign and a unit monomial. The differential identity
uses conjugated weights, so it applies to Laurent dagger rather than
only to ordinary transpose.
-/

namespace Decoupling.HighDim.Toric.Hodge

open Koszul

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable (K : Type) [CommRing K] {D k l : ℕ}

def dualLattice (h : k + l = D) : Term (Laurent K D) D k ≃ₗ[Laurent K D]
    Module.Dual (Laurent K D) (Term (Laurent K D) D l) :=
  (laurentGauge K k).trans (duality (Laurent K D) h)

theorem dualLattice_boundary (h : k + 1 + l = D) :
    (dualLattice K (by omega : k + (l + 1) = D)).toLinearMap.comp
        (boundary (Laurent K D) (difference K) k).hom =
      (boundary (Laurent K D) (fun i => bar (difference K i)) l).hom.dualMap.comp
        (dualLattice K h).toLinearMap := by
  apply LinearMap.ext
  intro x
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, dualLattice,
    LinearEquiv.trans_apply]
  have hg := congrArg (fun L => L x) (laurentGauge_boundary K k)
  have hd := congrArg (fun L => L (laurentGauge K (k + 1) x))
    (duality_boundary (Laurent K D) (fun i => bar (difference K i)) h)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hg hd
  rw [← hg]
  exact hd

theorem dualLattice_apply_complement_single (h : k + l = D)
    (x : Term (Laurent K D) D k) (I : Cell D k) (a : Laurent K D) :
    dualLattice K h x (Finsupp.single (complement h I) a) =
      a * orientation (Laurent K D) I * (cellUnit (Laurent K D) (directionUnit K) I : Laurent K D) * x I := by
  change duality (Laurent K D) h (laurentGauge K k x)
    (Finsupp.single (complement h I) a) = _
  rw [duality_apply_complement_single]
  simp only [laurentGauge, gauge_apply, mul_assoc]

end
end Decoupling.HighDim.Toric.Hodge
