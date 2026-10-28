import Decoupling.HighDim.GluedExact
import Decoupling.HighDim.ToricBoundaryCoordinates
import Decoupling.HighDim.ToricTopology

/-!
# The second Koszul exactness in the example's explicit coordinates

This transports the proved signed Hodge dual exactness through genuine
cell-enumeration equivalences. It does not assume a dual exactness certificate.
-/

namespace Decoupling.HighDim.Glued

open Matrix Koszul
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def nativeCellRelabel {k n : ℕ} (e : Fin n ≃ Cell 3 k) : Fin n ≃ Fin (Toric.cellCount 3 k) :=
  e.trans (Fintype.equivFin _)

variable (K : Type) [CommRing K]

theorem coordinateBoundary_eq_native {k m n : ℕ}
    (e : Fin m ≃ Cell 3 k) (f : Fin n ≃ Cell 3 (k + 1)) :
    coordinateBoundary (Laurent K 3) (difference K) e f =
      (Toric.boundaryMatrix K 3 k).submatrix (nativeCellRelabel e) (nativeCellRelabel f) := by
  apply Matrix.ext
  intro i j
  rw [coordinateBoundary_entry]
  change _ = Toric.weightedBoundaryMatrix K (difference K) k
    (nativeCellRelabel e i) (nativeCellRelabel f j)
  rw [Toric.weightedBoundaryMatrix_entry]
  simp [nativeCellRelabel]

variable [IsDomain K]

theorem coordinate_dual_exact {k m n l : ℕ} (hk : k + 1 < 3)
    (e : Fin m ≃ Cell 3 k) (f : Fin n ≃ Cell 3 (k + 1)) (g : Fin l ≃ Cell 3 (k + 2))
    (v : Fin n → Laurent K 3) :
    dagger (coordinateBoundary (Laurent K 3) (difference K) f g) *ᵥ v = 0 ↔
      ∃ z, dagger (coordinateBoundary (Laurent K 3) (difference K) e f) *ᵥ z = v := by
  have hc : coordinateBoundary (Laurent K 3) (difference K) e f *
      coordinateBoundary (Laurent K 3) (difference K) f g = 0 := by
    rw [coordinateBoundary_eq_native, coordinateBoundary_eq_native, Matrix.submatrix_mul_equiv]
    have h := Toric.checks_commute K 3 k
    rw [Toric.checks_H_X, Toric.checks_dagger_H_Z] at h
    rw [h]
    rfl
  constructor
  · intro hv
    rw [coordinateBoundary_eq_native] at hv
    change (dagger (Toric.boundaryMatrix K 3 (k + 1))).submatrix
      (nativeCellRelabel g) (nativeCellRelabel f) *ᵥ v = 0 at hv
    rw [Matrix.submatrix_mulVec_equiv] at hv
    have hv' : dagger (Toric.boundaryMatrix K 3 (k + 1)) *ᵥ
        (v ∘ (nativeCellRelabel f).symm) = 0 := by
      funext i
      simpa only [Function.comp_apply, Equiv.apply_symm_apply, Pi.zero_apply] using
        congrFun hv ((nativeCellRelabel g).symm i)
    obtain ⟨z, hz⟩ := (CSS.Checks.exact_Z (Toric.checks K 3 k)
      (Toric.checks_topological K 3 k hk) _).mp hv'
    refine ⟨z ∘ nativeCellRelabel e, ?_⟩
    rw [coordinateBoundary_eq_native]
    change (dagger (Toric.boundaryMatrix K 3 k)).submatrix
      (nativeCellRelabel f) (nativeCellRelabel e) *ᵥ (z ∘ nativeCellRelabel e) = v
    rw [Matrix.submatrix_mulVec_equiv]
    have hfun : (z ∘ nativeCellRelabel e) ∘ (nativeCellRelabel e).symm = z := by
      funext i
      simp
    rw [hfun]
    change dagger (Toric.boundaryMatrix K 3 k) *ᵥ z = v ∘ (nativeCellRelabel f).symm at hz
    rw [hz]
    funext i
    simp
  · rintro ⟨z, rfl⟩
    rw [Matrix.mulVec_mulVec, ← dagger_mul, hc]
    simp

theorem first_dual_exact (v : Fin 3 → Laurent K 3) :
    dagger (secondBoundary (Laurent K 3) (difference K)) *ᵥ v = 0 ↔
      ∃ z, dagger (firstBoundary (Laurent K 3) (difference K)) *ᵥ z = v := by
  simpa only [firstBoundary_coordinates, secondBoundary_coordinates] using
    coordinate_dual_exact K (by decide : 0 + 1 < 3) vertexEquiv edgeEquiv plaquetteEquiv v

theorem second_dual_exact (v : Fin 3 → Laurent K 3) :
    dagger (thirdBoundary (Laurent K 3) (difference K)) *ᵥ v = 0 ↔
      ∃ z, dagger (secondBoundary (Laurent K 3) (difference K)) *ᵥ z = v := by
  simpa only [secondBoundary_coordinates, thirdBoundary_coordinates] using
    coordinate_dual_exact K (by decide : 1 + 1 < 3) edgeEquiv plaquetteEquiv cubeEquiv v

end
end Decoupling.HighDim.Glued
