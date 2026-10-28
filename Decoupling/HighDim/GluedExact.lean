import Decoupling.HighDim.GluedCells

/-!
# Exactness in the paper's explicit three-dimensional cell coordinates

The polynomial matrices are transported from the actual signed Laurent
Koszul complex. Their exactness is a theorem, not input data for the
glued-code example.
-/

namespace Decoupling.HighDim.Glued

open CategoryTheory Matrix Koszul
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type*) [CommRing K] [IsDomain K]

theorem coordinate_exact {k m n l : ℕ}
    (e : Fin m ≃ Cell 3 k) (f : Fin n ≃ Cell 3 (k + 1)) (g : Fin l ≃ Cell 3 (k + 2))
    (v : Fin n → Laurent K 3) :
    coordinateBoundary (Laurent K 3) (difference K) e f *ᵥ v = 0 ↔
      ∃ z, coordinateBoundary (Laurent K 3) (difference K) f g *ᵥ z = v := by
  constructor
  · intro hv
    rw [coordinateBoundary_apply] at hv
    have hzero := (coordinates (Laurent K 3) e).map_eq_zero_iff.mp hv
    obtain ⟨z, hz⟩ := laurent_exact K 3 k ((coordinates (Laurent K 3) f).symm v) hzero
    refine ⟨coordinates (Laurent K 3) g z, ?_⟩
    rw [coordinateBoundary_apply, LinearEquiv.symm_apply_apply, hz,
      LinearEquiv.apply_symm_apply]
  · rintro ⟨z, rfl⟩
    rw [coordinateBoundary_apply, coordinateBoundary_apply, LinearEquiv.symm_apply_apply]
    have h := congrArg (fun L => L ((coordinates (Laurent K 3) g).symm z))
      (boundary_squared (Laurent K 3) (difference K) k)
    exact (congrArg (coordinates (Laurent K 3) e) h).trans (map_zero _)

theorem first_exact (v : Fin 3 → Laurent K 3) :
    firstBoundary (Laurent K 3) (difference K) *ᵥ v = 0 ↔
      ∃ z, secondBoundary (Laurent K 3) (difference K) *ᵥ z = v := by
  simpa only [firstBoundary_coordinates, secondBoundary_coordinates] using
    coordinate_exact K vertexEquiv edgeEquiv plaquetteEquiv v

theorem second_exact (v : Fin 3 → Laurent K 3) :
    secondBoundary (Laurent K 3) (difference K) *ᵥ v = 0 ↔
      ∃ z, thirdBoundary (Laurent K 3) (difference K) *ᵥ z = v := by
  simpa only [secondBoundary_coordinates, thirdBoundary_coordinates] using
    coordinate_exact K edgeEquiv plaquetteEquiv cubeEquiv v

end
end Decoupling.HighDim.Glued
