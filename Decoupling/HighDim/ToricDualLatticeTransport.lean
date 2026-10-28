import Decoupling.HighDim.ToricDualLatticeUnitary

/-!
# Both stabilizer modules under complementary dual-cell relabeling

For `k+l+2=D`, the actual `(k+1)`-form code with X/Z exchanged becomes
the actual `(l+1)`-form code. The qudit map is the explicit unitary
signed monomial permutation, so its X and Z label actions coincide.
This is a geometric dual-lattice identification, not an assertion that
an arbitrary cell translation is a same-lattice finite-depth circuit.
-/

namespace Decoupling.HighDim.Toric

open Matrix Koszul

noncomputable section
variable (K : Type) [CommRing K] {D k l : ℕ}

theorem dualLatticeMatrix_coboundary (h : k + l + 2 = D) :
    dualLatticeMatrix K (by omega : (k + 1) + (l + 1) = D) * dagger (boundaryMatrix K D k) =
      boundaryMatrix K D (l + 1) * dualLatticeMatrix K (by omega : k + (l + 2) = D) := by
  have he := congrArg dagger
    (dualLatticeMatrix_boundary K (by omega : k + 1 + (l + 1) = D))
  simp only [dagger_mul, dagger_dagger] at he
  have hm := congrArg (fun B => dualLatticeMatrix K (by omega : (k + 1) + (l + 1) = D) * B *
    dualLatticeMatrix K (by omega : k + (l + 2) = D)) he
  simp only [Matrix.mul_assoc] at hm
  rw [dualLatticeMatrix_dagger_mul, Matrix.mul_one] at hm
  simpa only [← Matrix.mul_assoc, dualLatticeMatrix_mul_dagger, Matrix.one_mul] using hm

private theorem image_transport
    {a b c d : ℕ} (U : Matrix (Fin b) (Fin a) (Laurent K D))
    (B : Matrix (Fin a) (Fin c) (Laurent K D))
    (B' : Matrix (Fin b) (Fin d) (Laurent K D))
    (P : CSS.Free K D c ≃ₗ[Laurent K D] CSS.Free K D d)
    (hs : ∀ z, U *ᵥ (B *ᵥ z) = B' *ᵥ P z) (v : CSS.Free K D b) :
    (∃ z, U *ᵥ (B *ᵥ z) = v) ↔ ∃ z, B' *ᵥ z = v := by
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨P z, (hs z).symm.trans hz⟩
  · rintro ⟨z, hz⟩
    refine ⟨P.symm z, ?_⟩
    rw [hs, LinearEquiv.apply_symm_apply, hz]

/-- The actual Z-stabilizer module after sector exchange. -/
theorem dualLattice_z_stabilizers (h : k + l + 2 = D)
    (v : CSS.Free K D (cellCount D (l + 1))) :
    (∃ z, dualLatticeMatrix K (by omega : (k + 1) + (l + 1) = D) *ᵥ
      (dagger (checks K D k).swap.H_Z *ᵥ z) = v) ↔
        ∃ z, dagger (checks K D l).H_Z *ᵥ z = v := by
  change (∃ z, dualLatticeMatrix K _ *ᵥ (dagger (boundaryMatrix K D k) *ᵥ z) = v) ↔ _
  rw [checks_dagger_H_Z]
  apply image_transport K _ _ _
    (dualLatticeCoordinates K (by omega : k + (l + 2) = D))
  intro z
  rw [Matrix.mulVec_mulVec, dualLatticeMatrix_coboundary K h, ← Matrix.mulVec_mulVec,
    dualLatticeMatrix_mulVec]

/-- The actual X-stabilizer module uses the same map because its proved
inverse dagger equals the map itself. -/
theorem dualLattice_x_stabilizers (h : k + l + 2 = D)
    (v : CSS.Free K D (cellCount D (l + 1))) :
    (∃ z, dualLatticeMatrix K (by omega : (k + 1) + (l + 1) = D) *ᵥ
      (dagger (checks K D k).swap.H_X *ᵥ z) = v) ↔
        ∃ z, dagger (checks K D l).H_X *ᵥ z = v := by
  change (∃ z, dualLatticeMatrix K _ *ᵥ (dagger (checks K D k).H_Z *ᵥ z) = v) ↔ _
  rw [checks_dagger_H_Z, checks_H_X]
  apply image_transport K _ _ _
    (dualLatticeCoordinates K (by omega : (k + 2) + l = D))
  intro z
  rw [Matrix.mulVec_mulVec, dualLatticeMatrix_boundary K (by omega : (k + 1) + 1 + l = D),
    ← Matrix.mulVec_mulVec, dualLatticeMatrix_mulVec]

end
end Decoupling.HighDim.Toric
