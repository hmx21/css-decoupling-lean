import Decoupling.Circuit
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Genuine finite-qubit permutation unitaries and Pauli conjugation

The computational basis is indexed by binary configurations.  A bijective
binary linear map acts by an actual permutation of that basis, producing both
a complex unitary matrix and a linear isometry of the finite Hilbert space.
Pure X and pure Z conjugation identities are exact, including their phases.
The finite CNOT has the same target-row/control-column convention as `Circuit`.
-/

namespace Decoupling.PauliUnitary

open Matrix

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Bits (ι : Type*) := ι → ZMod 2
abbrev State (ι : Type*) := Bits ι → ℂ
abbrev Hilbert (ι : Type*) [Fintype ι] := EuclideanSpace ℂ (Bits ι)

/-- The computational ket, in explicit complex coordinates. -/
def ket (s : Bits ι) : State ι := Pi.single s 1

/-- The inverse in this definition makes the matrix send `|s⟩` to `|e s⟩`. -/
def permutation (e : Bits ι ≃ Bits ι) : Matrix (Bits ι) (Bits ι) ℂ :=
  Equiv.Perm.permMatrix ℂ e.symm

@[simp]
theorem permutation_apply (e : Bits ι ≃ Bits ι) (ψ : State ι) (s : Bits ι) :
    (permutation e *ᵥ ψ) s = ψ (e.symm s) := by
  exact congrFun (Matrix.permMatrix_mulVec (R := ℂ) (v := ψ) e.symm) s

omit [DecidableEq ι] in
@[simp]
theorem permutation_adjoint (e : Bits ι ≃ Bits ι) :
    (permutation e)ᴴ = permutation e.symm := by
  simp [permutation, Equiv.Perm.inv_def]

/-- Actual complex unitarity, rather than preservation of a binary support form. -/
theorem permutation_unitary (e : Bits ι ≃ Bits ι) :
    (permutation e)ᴴ * permutation e = 1 := by
  rw [permutation_adjoint]
  change Equiv.Perm.permMatrix ℂ e * Equiv.Perm.permMatrix ℂ e.symm = 1
  rw [← Matrix.permMatrix_mul]
  simp [Equiv.Perm.mul_def]

def permutationUnitary (e : Bits ι ≃ Bits ι) : Matrix.unitaryGroup (Bits ι) ℂ :=
  ⟨permutation e, Matrix.mem_unitaryGroup_iff'.mpr (permutation_unitary e)⟩

/-- The corresponding unitary on the actual finite-dimensional complex Hilbert space. -/
def hilbertPermutation (e : Bits ι ≃ Bits ι) : Hilbert ι ≃ₗᵢ[ℂ] Hilbert ι :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ e

@[simp]
theorem hilbertPermutation_apply (e : Bits ι ≃ Bits ι) (ψ : Hilbert ι) (s : Bits ι) :
    hilbertPermutation e ψ s = (permutation e *ᵥ (fun t => ψ t)) s := by
  rw [permutation_apply]
  rfl

theorem permutation_ket (e : Bits ι ≃ Bits ι) (s : Bits ι) :
    permutation e *ᵥ ket s = ket (e s) := by
  funext t
  simp only [permutation_apply, ket, Pi.single_apply]
  simp only [e.symm_apply_eq]

/-- Binary translation implements the product of X operators on support a. -/
def translation (a : Bits ι) : Bits ι ≃ Bits ι :=
  Function.Involutive.toPerm (fun s => s + a) (fun s => by
    funext i
    exact CharTwo.add_cancel_right (s i) (a i))

def X (a : Bits ι) : Matrix (Bits ι) (Bits ι) ℂ := permutation (translation a)

/-- The real character of the binary phase bit. -/
def sign (b : ZMod 2) : ℂ := if b = 0 then 1 else -1

@[simp] theorem sign_zero : sign 0 = 1 := by simp [sign]
@[simp] theorem sign_one : sign 1 = -1 := by simp [sign]

def Z (b : Bits ι) : Matrix (Bits ι) (Bits ι) ℂ :=
  Matrix.diagonal (fun s => sign (b ⬝ᵥ s))

@[simp]
theorem X_apply (a : Bits ι) (ψ : State ι) (s : Bits ι) :
    (X a *ᵥ ψ) s = ψ (s + a) := permutation_apply _ _ _

@[simp]
theorem Z_apply (b : Bits ι) (ψ : State ι) (s : Bits ι) :
    (Z b *ᵥ ψ) s = sign (b ⬝ᵥ s) * ψ s := Matrix.mulVec_diagonal _ _ _

theorem X_ket (a s : Bits ι) : X a *ᵥ ket s = ket (s + a) :=
  permutation_ket (translation a) s

theorem Z_ket (b s : Bits ι) : Z b *ᵥ ket s = sign (b ⬝ᵥ s) • ket s := by
  funext t
  by_cases h : t = s
  · subst t
    simp [ket]
  · simp [ket, h]


/-- Binary support addition is exactly multiplication of pure X Paulis. -/
theorem X_add (a b : Bits ι) : X (a + b) = X a * X b := by
  apply Matrix.mulVec_injective
  funext ψ s
  simp only [← Matrix.mulVec_mulVec, X_apply, add_assoc]

/-- The binary phase is a genuine character into the complex units. -/
theorem sign_add (a b : ZMod 2) : sign (a + b) = sign a * sign b := by
  fin_cases a <;> fin_cases b <;> norm_num [sign]
  exact (show (2 : ZMod 2) = 0 from by decide)

/-- Binary support addition is exactly multiplication of pure Z Paulis. -/
theorem Z_add (a b : Bits ι) : Z (a + b) = Z a * Z b := by
  apply Matrix.mulVec_injective
  funext ψ s
  simp only [← Matrix.mulVec_mulVec, Z_apply, add_dotProduct, sign_add, mul_assoc]

/-- Pure X Paulis are actual complex unitary matrices. -/
theorem X_unitary (a : Bits ι) : (X a)ᴴ * X a = 1 :=
  permutation_unitary (translation a)

/-- The binary phase character takes only real unit values. -/
theorem sign_star_mul (b : ZMod 2) : star (sign b) * sign b = 1 := by
  by_cases h : b = 0 <;> simp [sign, h]

/-- Pure Z Paulis are actual complex unitary matrices. -/
theorem Z_unitary (b : Bits ι) : (Z b)ᴴ * Z b = 1 := by
  simp only [Z, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
  have h : (fun s : Bits ι => star (sign (b ⬝ᵥ s)) * sign (b ⬝ᵥ s)) = fun _ => 1 := by
    funext s
    exact sign_star_mul _
  change Matrix.diagonal (fun s : Bits ι => star (sign (b ⬝ᵥ s)) * sign (b ⬝ᵥ s)) = 1
  rw [h, Matrix.diagonal_one]

variable (U : Bits ι ≃ₗ[ZMod 2] Bits ι)

/-- The literal inverse-transpose support action, in the column convention. -/
def inverseTranspose (b : Bits ι) : Bits ι :=
  (LinearMap.toMatrix' U.symm.toLinearMap)ᵀ *ᵥ b

theorem inverseTranspose_pairing (b s : Bits ι) :
    inverseTranspose U b ⬝ᵥ s = b ⬝ᵥ U.symm s := by
  rw [dotProduct_comm]
  unfold inverseTranspose
  rw [Matrix.dotProduct_transpose_mulVec, LinearMap.toMatrix'_mulVec]
  rfl

/-- No extra sign occurs in conjugating a pure X Pauli. -/
theorem conjugate_X (a : Bits ι) :
    permutation U.toEquiv * X a * (permutation U.toEquiv)ᴴ = X (U a) := by
  apply Matrix.mulVec_injective
  funext ψ s
  simp only [← Matrix.mulVec_mulVec, permutation_adjoint, permutation_apply,
    X_apply, LinearEquiv.coe_toEquiv, Equiv.symm_symm]
  simp [map_add]

/-- No extra sign occurs in conjugating a pure Z Pauli. -/
theorem conjugate_Z (b : Bits ι) :
    permutation U.toEquiv * Z b * (permutation U.toEquiv)ᴴ = Z (inverseTranspose U b) := by
  apply Matrix.mulVec_injective
  funext ψ s
  simp only [← Matrix.mulVec_mulVec, permutation_adjoint, permutation_apply,
    Z_apply, LinearEquiv.coe_toEquiv, Equiv.symm_symm]
  rw [inverseTranspose_pairing]
  simp


section CNOT

variable (control target : ι)

/-- Finite CNOT: the target bit receives the control bit. -/
def cnotMatrix : Matrix ι ι (ZMod 2) := 1 + Matrix.single target control 1

theorem cnotMatrix_apply (s : Bits ι) (i : ι) :
    (cnotMatrix control target *ᵥ s) i = s i + if i = target then s control else 0 := by
  simp [cnotMatrix, Matrix.add_mulVec, Matrix.single_mulVec, Function.update_apply]


omit [Fintype ι] in
theorem cnotMatrix_transpose :
    (cnotMatrix control target)ᵀ = cnotMatrix target control := by
  ext i j
  simp [cnotMatrix, Matrix.single, Matrix.one_apply, and_comm, eq_comm]

theorem cnotMatrix_transpose_apply (s : Bits ι) (i : ι) :
    ((cnotMatrix control target)ᵀ *ᵥ s) i =
      s i + if i = control then s target else 0 := by
  rw [cnotMatrix_transpose, cnotMatrix_apply]

theorem cnotMatrix_involutive (h : control ≠ target) :
    cnotMatrix control target * cnotMatrix control target = 1 := by
  have hz : Matrix.single target control (1 : ZMod 2) * Matrix.single target control 1 = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _ h _
  simp only [cnotMatrix, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, hz, add_zero]
  have htwo : Matrix.single target control (1 : ZMod 2) + Matrix.single target control 1 = 0 := by
    funext i j
    exact CharTwo.add_self_eq_zero _
  rw [add_assoc, htwo, add_zero]

def cnot (h : control ≠ target) : Bits ι ≃ₗ[ZMod 2] Bits ι :=
  LinearEquiv.ofInvolutive (cnotMatrix control target).mulVecLin (fun s => by
    change cnotMatrix control target *ᵥ (cnotMatrix control target *ᵥ s) = s
    rw [Matrix.mulVec_mulVec, cnotMatrix_involutive control target h, Matrix.one_mulVec])

@[simp]
theorem cnot_apply (h : control ≠ target) (s : Bits ι) :
    cnot control target h s = cnotMatrix control target *ᵥ s := rfl

@[simp]
theorem cnot_symm (h : control ≠ target) : (cnot control target h).symm = cnot control target h := rfl

theorem cnot_inverseTranspose (h : control ≠ target) (b : Bits ι) :
    inverseTranspose (cnot control target h) b = (cnotMatrix control target)ᵀ *ᵥ b := by
  unfold inverseTranspose
  rw [cnot_symm]
  have hm : LinearMap.toMatrix' (cnot control target h).toLinearMap = cnotMatrix control target :=
    LinearMap.toMatrix'_toLin' _
  rw [hm]

/-- Exact finite CNOT X conjugation in the manuscript's column convention. -/
theorem cnot_conjugate_X (h : control ≠ target) (a : Bits ι) :
    permutation (cnot control target h).toEquiv * X a *
        (permutation (cnot control target h).toEquiv)ᴴ = X (cnotMatrix control target *ᵥ a) :=
  conjugate_X (cnot control target h) a

/-- Exact finite CNOT Z conjugation uses the inverse transpose, here its transpose. -/
theorem cnot_conjugate_Z (h : control ≠ target) (b : Bits ι) :
    permutation (cnot control target h).toEquiv * Z b *
        (permutation (cnot control target h).toEquiv)ᴴ = Z ((cnotMatrix control target)ᵀ *ᵥ b) := by
  rw [conjugate_Z, cnot_inverseTranspose]

omit [Fintype ι] in
/-- Evaluation at one removes the displacement while preserving Circuit's
literal target-row/control-column CNOT matrix. -/
theorem circuit_matrix_atOne (g : Circuit.CNOT ι) :
    g.xMatrix.map augmentation = cnotMatrix g.control g.target := by
  ext i j
  by_cases h : g.target = i ∧ g.control = j <;>
    simp [Circuit.CNOT.xMatrix, cnotMatrix, Matrix.single, Matrix.one_apply, h]

end CNOT

/-- The all-zero computational auxiliary state. -/
def zeroState : State ι := ket 0

/-- The normalized uniform superposition, the tensor product of |+⟩ states. -/
def plusState : State ι :=
  fun _ => ((Real.sqrt (Fintype.card (Bits ι) : ℝ))⁻¹ : ℂ)

theorem Z_zeroState (b : Bits ι) : Z b *ᵥ zeroState = zeroState := by
  simpa [zeroState] using Z_ket b (0 : Bits ι)

theorem X_plusState (a : Bits ι) : X a *ᵥ plusState = plusState := by
  funext s
  rw [X_apply]
  rfl

theorem zeroState_norm : ‖WithLp.toLp 2 (zeroState (ι := ι))‖ = 1 := by
  change ‖(EuclideanSpace.single (0 : Bits ι) (1 : ℂ))‖ = 1
  simp

theorem plusState_norm : ‖WithLp.toLp 2 (plusState (ι := ι))‖ = 1 := by
  have hc : (0 : ℝ) < Fintype.card (Bits ι) := by exact_mod_cast Fintype.card_pos
  rw [EuclideanSpace.norm_eq]
  simp only [plusState, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, inv_pow]
  rw [Real.sq_sqrt hc.le, mul_inv_cancel₀ (ne_of_gt hc), Real.sqrt_one]

end
end Decoupling.PauliUnitary
