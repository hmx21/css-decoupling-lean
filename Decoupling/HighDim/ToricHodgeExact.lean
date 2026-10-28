import Decoupling.HighDim.ToricHodgeDifferential
import Decoupling.HighDim.KoszulExact

/-!
# Exactness of the actual dual Laurent Koszul complex below top degree

The signed perfect pairing transports the already proved primal
exactness. No dual exactness, grade, or Ext-vanishing assumption is used.
-/

namespace Decoupling.HighDim.Toric.Hodge

open Koszul

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type*) [CommRing K] [IsDomain K] {D k l : ℕ}

theorem dual_exact (h : k + l + 2 = D)
    (f : Module.Dual (Laurent K D) (Term (Laurent K D) D (k + 1)))
    (hf : (boundary (Laurent K D) (difference K) (k + 1)).hom.dualMap f = 0) :
    ∃ g : Module.Dual (Laurent K D) (Term (Laurent K D) D k),
      (boundary (Laurent K D) (difference K) k).hom.dualMap g = f := by
  let v := (duality (Laurent K D) (by omega : l + 1 + (k + 1) = D)).symm f
  have hv : (boundary (Laurent K D) (difference K) l).hom v = 0 := by
    apply (duality (Laurent K D) (by omega : l + (k + 2) = D)).injective
    rw [map_zero]
    have he := congrArg (fun L => L v)
      (duality_boundary (Laurent K D) (difference K) (by omega : l + 1 + (k + 1) = D))
    change duality (Laurent K D) _ ((boundary (Laurent K D) (difference K) l).hom v) =
      (boundary (Laurent K D) (difference K) (k + 1)).hom.dualMap
        (duality (Laurent K D) _ v) at he
    simpa only [v, LinearEquiv.apply_symm_apply, hf] using he
  obtain ⟨z, hz⟩ := laurent_exact K D l v hv
  refine ⟨duality (Laurent K D) (by omega : l + 2 + k = D) z, ?_⟩
  have he := congrArg (fun L => L z)
    (duality_boundary (Laurent K D) (difference K) (by omega : (l + 1) + 1 + k = D))
  change duality (Laurent K D) _ ((boundary (Laurent K D) (difference K) (l + 1)).hom z) =
    (boundary (Laurent K D) (difference K) k).hom.dualMap
      (duality (Laurent K D) _ z) at he
  rw [hz] at he
  exact he.symm.trans (LinearEquiv.apply_symm_apply _ f)

end
end Decoupling.HighDim.Toric.Hodge
