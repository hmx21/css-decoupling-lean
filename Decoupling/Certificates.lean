import Decoupling.Laurent
import Decoupling.Stabilization

/-!
# Stabilizer-image certificates

These are the image-transport arguments of Proposition IV.2, with exactness
explicitly supplied. They do not assert that the input satisfies the
topological assumptions, or that comparison data always exist.
`inImage B v` means membership in the column-generated submodule im B.
-/

namespace Decoupling
namespace Certificates

open Matrix

def inImage {m n : Type*} [Fintype n] (B : Matrix m n R) (v : m → R) : Prop :=
  ∃ z, B *ᵥ z = v

variable {Q Q' C C' Z Z' : Type*}
  [Fintype Q] [Fintype Q'] [Fintype C] [Fintype C'] [Fintype Z] [Fintype Z']
  [DecidableEq Q] [DecidableEq Q'] [DecidableEq C] [DecidableEq C']

omit [DecidableEq Q] [DecidableEq Q'] [DecidableEq C'] in
/-- An invertible commuting square transports the physical kernel. -/
theorem kernel_transport
    (H : Matrix C Q R) (H' : Matrix C' Q' R)
    (U : Matrix Q' Q R) (P : Matrix C' C R) (Pinv : Matrix C C' R)
    (hP : Pinv * P = 1) (square : H' * U = P * H) (v : Q → R) :
    H' *ᵥ (U *ᵥ v) = 0 ↔ H *ᵥ v = 0 := by
  rw [mulVec_mulVec, square, ← mulVec_mulVec]
  constructor
  · intro h
    have hh := congrArg (fun w => Pinv *ᵥ w) h
    simpa [mulVec_mulVec, ← Matrix.mul_assoc, hP] using hh
  · intro h
    simp [h]

omit [DecidableEq Q] [DecidableEq C'] in
/-- First identity in equation (61), given the two physical exactness equalities. -/
theorem z_image_certificate
    (H : Matrix C Q R) (H' : Matrix C' Q' R)
    (B : Matrix Q Z R) (B' : Matrix Q' Z' R)
    (U : Matrix Q' Q R) (Uinv : Matrix Q Q' R)
    (P : Matrix C' C R) (Pinv : Matrix C C' R)
    (hU : U * Uinv = 1) (hP : Pinv * P = 1)
    (square : H' * U = P * H)
    (exactF : ∀ v, H *ᵥ v = 0 ↔ inImage B v)
    (exactG : ∀ v, H' *ᵥ v = 0 ↔ inImage B' v) (v : Q' → R) :
    (∃ z, U *ᵥ (B *ᵥ z) = v) ↔ inImage B' v := by
  constructor
  · rintro ⟨z, rfl⟩
    apply (exactG _).mp
    apply (kernel_transport H H' U P Pinv hP square _).mpr
    exact (exactF _).mpr ⟨z, rfl⟩
  · intro h
    have hUv : U *ᵥ (Uinv *ᵥ v) = v := by simp [mulVec_mulVec, hU]
    have hz : H *ᵥ (Uinv *ᵥ v) = 0 :=
      (kernel_transport H H' U P Pinv hP square _).mp
        (by rw [hUv]; exact (exactG _).mpr h)
    obtain ⟨z, hz⟩ := (exactF _).mp hz
    exact ⟨z, by rw [hz, hUv]⟩

omit [Fintype C'] [DecidableEq Q] [DecidableEq C] [DecidableEq C'] in
/-- The dagger identity used in the second half of Proposition IV.2. -/
theorem dagger_check_identity
    (H : Matrix C Q R) (H' : Matrix C' Q' R)
    (U : Matrix Q' Q R) (Uinv : Matrix Q Q' R) (P : Matrix C' C R)
    (hU : U * Uinv = 1) (square : H' * U = P * H) :
    dagger H' = dagger Uinv * dagger H * dagger P := by
  have h : H' = P * H * Uinv := by
    rw [← square, Matrix.mul_assoc, hU, Matrix.mul_one]
  rw [h, dagger_mul, dagger_mul, Matrix.mul_assoc]

omit [DecidableEq Q] [DecidableEq C'] in
/-- Second identity in equation (61); the X action is (U⁻¹)†. -/
theorem x_image_certificate
    (H : Matrix C Q R) (H' : Matrix C' Q' R)
    (U : Matrix Q' Q R) (Uinv : Matrix Q Q' R)
    (P : Matrix C' C R) (Pinv : Matrix C C' R)
    (hU : U * Uinv = 1) (hP : Pinv * P = 1)
    (square : H' * U = P * H) (v : Q' → R) :
    (∃ z, dagger Uinv *ᵥ (dagger H *ᵥ z) = v) ↔ inImage (dagger H') v := by
  have hdag := dagger_check_identity H H' U Uinv P hU square
  have hdagP : dagger P * dagger Pinv = 1 := by
    rw [← dagger_mul, hP, dagger_one]
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨dagger Pinv *ᵥ z, ?_⟩
    rw [hdag]
    simp only [← mulVec_mulVec]
    rw [mulVec_mulVec z (dagger P) (dagger Pinv), hdagP, one_mulVec]
  · rintro ⟨z, hz⟩
    refine ⟨dagger P *ᵥ z, ?_⟩
    rw [hdag] at hz
    simpa only [mulVec_mulVec, Matrix.mul_assoc] using hz

end Certificates
end Decoupling
