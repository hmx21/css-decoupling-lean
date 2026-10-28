import Decoupling.HighDim.CorollaryOneZ

/-!
# Physical meaning of the odd-characteristic orientation sign

The signed monomial in the dual-cell identification is a displacement and
an on-site change of computational basis. Its minus sign is implemented
by the actual permutation |a⟩ ↦ |(-1)^n a⟩ and acts with the same sign on
both Pauli labels. It is not silently dropped in characteristic other than 2.
-/

namespace Decoupling.HighDim.PauliUnitary

open Matrix
noncomputable section

variable {p : ℕ} [NeZero p]

omit [NeZero p] in
theorem orientationSign_square (n : ℕ) :
    (-1 : ZMod p) ^ n * (-1 : ZMod p) ^ n = 1 := by
  rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]

/-- A real single-qudit computational-basis permutation implementing the
orientation sign, with its inverse proved explicitly. -/
def orientationGate (n : ℕ) : Config p Unit ≃ₗ[ZMod p] Config p Unit where
  toFun a i := (-1 : ZMod p) ^ n * a i
  invFun a i := (-1 : ZMod p) ^ n * a i
  left_inv a := by
    ext i
    change (-1 : ZMod p) ^ n * ((-1 : ZMod p) ^ n * a i) = a i
    rw [← mul_assoc, orientationSign_square, one_mul]
  right_inv a := by
    ext i
    change (-1 : ZMod p) ^ n * ((-1 : ZMod p) ^ n * a i) = a i
    rw [← mul_assoc, orientationSign_square, one_mul]
  map_add' a b := by ext i; exact mul_add _ _ _
  map_smul' c a := by ext i; change _ * (c * a i) = c * (_ * a i); ring

/-- This is membership in the actual complex unitary group. -/
def orientationUnitary (n : ℕ) : Matrix.unitaryGroup (Config p Unit) ℂ :=
  permutationUnitary (orientationGate (p := p) n).toEquiv

omit [NeZero p] in
theorem orientationGate_inverseTranspose (n : ℕ) (b : Config p Unit) :
    inverseTranspose (orientationGate n) b = orientationGate n b := by
  funext i
  cases i
  simp [inverseTranspose, orientationGate, LinearMap.toMatrix'_apply,
    Matrix.mulVec, dotProduct]

theorem orientation_conjugate_X (n : ℕ) (a : Config p Unit) :
    permutation (orientationGate n).toEquiv * X a *
      (permutation (orientationGate n).toEquiv)ᴴ =
        X (fun i => (-1 : ZMod p) ^ n * a i) :=
  conjugate_X (orientationGate n) a

theorem orientation_conjugate_Z (n : ℕ) (b : Config p Unit) :
    permutation (orientationGate n).toEquiv * Z b *
      (permutation (orientationGate n).toEquiv)ᴴ =
        Z (fun i => (-1 : ZMod p) ^ n * b i) := by
  rw [conjugate_Z, orientationGate_inverseTranspose]
  rfl

end
end Decoupling.HighDim.PauliUnitary
