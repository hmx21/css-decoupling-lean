import Decoupling.HighDim.ProductStates
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Normalized finite qudit Fourier transform

The sign convention is `F[s,t] = |Config|^(-1/2) exp(2πi (s·t)/p)`.
Consequently `F X(a) F† = Z(a)` and `F Z(b) F† = X(-b)`.
These are actual complex matrix identities, including odd-prime signs.
All finite site sets, including the empty set, are admitted.
-/

noncomputable section
namespace Decoupling.HighDim.PauliUnitary

open Matrix

variable {p : ℕ} [NeZero p] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem phase_star (b : ZMod p) : star (phase b) = phase (-b) := by
  change star (ZMod.toCircle b : ℂ) = (ZMod.toCircle (-b) : ℂ)
  rw [AddChar.map_neg_eq_inv]
  exact (Circle.coe_inv_eq_conj _).symm

theorem phase_sub (a b : ZMod p) : phase (a - b) = phase a * star (phase b) := by
  rw [sub_eq_add_neg, phase_add, phase_star]

def dotCharacter (a : Config p ι) : AddChar (Config p ι) ℂ where
  toFun b := phase (a ⬝ᵥ b)
  map_zero_eq_one' := by simp
  map_add_eq_mul' x y := by rw [dotProduct_add, phase_add]

theorem character_sum (a : Config p ι) :
    ∑ b : Config p ι, phase (a ⬝ᵥ b) =
      if a = 0 then (Fintype.card (Config p ι) : ℂ) else 0 := by
  by_cases ha : a = 0
  · subst a
    simp
  · rw [ite_eq_right ha]
    apply AddChar.sum_eq_zero_of_ne_one (ψ := dotCharacter a)
    intro h
    obtain ⟨i, hi⟩ : ∃ i, a i ≠ 0 := by
      by_contra! hh
      exact ha (funext hh)
    have h' := congrArg (fun f : AddChar (Config p ι) ℂ => f (Pi.single i 1)) h
    have hh : phase (a i) = 1 := by
      simpa [dotCharacter, dotProduct_single] using h'
    exact hi ((phase_eq_one _).mp hh)

def fourierScale : ℂ := ((Real.sqrt (Fintype.card (Config p ι) : ℝ))⁻¹ : ℂ)

theorem fourierScale_star : star (fourierScale (p := p) (ι := ι)) = fourierScale (p := p) (ι := ι) := by
  simp [fourierScale]

theorem fourierScale_square_card :
    fourierScale (p := p) (ι := ι) * fourierScale (p := p) (ι := ι) * Fintype.card (Config p ι) = 1 := by
  have hc : (0 : ℝ) < Fintype.card (Config p ι) := by exact_mod_cast Fintype.card_pos
  have hs : (Real.sqrt (Fintype.card (Config p ι) : ℝ) : ℂ) ^ 2 =
      Fintype.card (Config p ι) := by exact_mod_cast Real.sq_sqrt hc.le
  have hn : (Fintype.card (Config p ι) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hc
  change (Real.sqrt (Fintype.card (Config p ι) : ℝ) : ℂ)⁻¹ *
    (Real.sqrt (Fintype.card (Config p ι) : ℝ) : ℂ)⁻¹ * _ = 1
  rw [← pow_two, inv_pow, hs, inv_mul_cancel₀ hn]

def fourier : Matrix (Config p ι) (Config p ι) ℂ :=
  fun s t => fourierScale (p := p) (ι := ι) * phase (s ⬝ᵥ t)

theorem fourier_unitary : (fourier (p := p) (ι := ι))ᴴ * fourier = 1 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hterm (s : Config p ι) :
      (fourier (p := p) (ι := ι))ᴴ a s * fourier s b =
        (fourierScale (p := p) (ι := ι) * fourierScale (p := p) (ι := ι)) * phase ((b - a) ⬝ᵥ s) := by
    simp only [Matrix.conjTranspose_apply, fourier, star_mul, fourierScale_star,
      sub_dotProduct, phase_sub]
    rw [dotProduct_comm b s, dotProduct_comm a s]
    ring
  simp_rw [hterm]
  rw [← Finset.mul_sum, character_sum]
  by_cases h : a = b
  · subst b
    simpa using (fourierScale_square_card (p := p) (ι := ι))
  · rw [ite_eq_right (sub_ne_zero.mpr (Ne.symm h)), mul_zero, ite_eq_right h]

theorem fourier_mul_adjoint : fourier (p := p) (ι := ι) * fourierᴴ = 1 :=
  mul_eq_one_comm.mp fourier_unitary

def fourierUnitary : Matrix.unitaryGroup (Config p ι) ℂ :=
  ⟨fourier, Matrix.mem_unitaryGroup_iff'.mpr fourier_unitary⟩

/-- Fourier as an actual linear automorphism of the finite complex Hilbert space. -/
def hilbertFourierLinear : Hilbert p ι ≃ₗ[ℂ] Hilbert p ι :=
  (WithLp.linearEquiv 2 ℂ (State p ι)).trans
    ((Matrix.UnitaryGroup.toLinearEquiv (fourierUnitary (p := p) (ι := ι))).trans
      (WithLp.linearEquiv 2 ℂ (State p ι)).symm)

/-- Inner products use the Euclidean Hilbert norm, not the sup norm on functions. -/
theorem hilbertFourier_inner (x y : Hilbert p ι) :
    inner ℂ (hilbertFourierLinear x) (hilbertFourierLinear y) = inner ℂ x y := by
  change (fourier *ᵥ (fun i => y i)) ⬝ᵥ star (fourier *ᵥ (fun i => x i)) =
    (fun i => y i) ⬝ᵥ star (fun i => x i)
  rw [dotProduct_comm, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, fourier_unitary, Matrix.one_mulVec, dotProduct_comm]

def hilbertFourier : Hilbert p ι ≃ₗᵢ[ℂ] Hilbert p ι where
  __ := hilbertFourierLinear
  norm_map' := (LinearMap.norm_map_iff_inner_map_map hilbertFourierLinear).mpr hilbertFourier_inner

theorem mul_permutation_apply (A : Matrix (Config p ι) (Config p ι) ℂ)
    (e : Config p ι ≃ Config p ι) (i j : Config p ι) :
    (A * permutation e) i j = A i (e j) := by
  exact congrFun (Matrix.vecMul_permMatrix e.symm (v := A i)) j

theorem permutation_mul_apply (A : Matrix (Config p ι) (Config p ι) ℂ)
    (e : Config p ι ≃ Config p ι) (i j : Config p ι) :
    (permutation e * A) i j = A (e.symm i) j := by
  exact congrFun (Matrix.permMatrix_mulVec e.symm (v := fun k => A k j)) i

theorem fourier_X_intertwine (a : Config p ι) : fourier * X a = Z a * fourier := by
  ext i j
  rw [X, mul_permutation_apply, Z, Matrix.diagonal_mul]
  simp only [fourier, translation, Equiv.coe_fn_mk, dotProduct_add, phase_add]
  rw [dotProduct_comm a i]
  ring

theorem fourier_Z_intertwine (b : Config p ι) : fourier * Z b = X (-b) * fourier := by
  ext i j
  rw [Z, Matrix.mul_diagonal, X, permutation_mul_apply]
  simp only [fourier, translation, Equiv.coe_fn_symm_mk, sub_neg_eq_add,
    add_dotProduct, phase_add]
  ring

theorem fourier_conjugate_X (a : Config p ι) : fourier * X a * fourierᴴ = Z a := by
  rw [fourier_X_intertwine, Matrix.mul_assoc, fourier_mul_adjoint, Matrix.mul_one]

theorem fourier_conjugate_Z (b : Config p ι) : fourier * Z b * fourierᴴ = X (-b) := by
  rw [fourier_Z_intertwine, Matrix.mul_assoc, fourier_mul_adjoint, Matrix.mul_one]

/-- Fourier changes a linear computational permutation to its inverse-transpose
permutation whenever the displayed pairing identity has been proved. -/
theorem fourier_linear_intertwine (U V : Config p ι ≃ₗ[ZMod p] Config p ι)
    (h : ∀ i j, i ⬝ᵥ U j = V.symm i ⬝ᵥ j) :
    fourier * permutation U.toEquiv = permutation V.toEquiv * fourier := by
  ext i j
  rw [mul_permutation_apply, permutation_mul_apply]
  exact congrArg (fun z => fourierScale (p := p) (ι := ι) * phase z) (h i j)

/-- Global on-site Fourier turns SUM(c→t,λ) into SUM(t→c,-λ), with no missing phase. -/
theorem fourier_conjugate_SUM (control target : ι) (weight : ZMod p)
    (h : control ≠ target) :
    fourier * permutation (sumGate control target weight h).toEquiv * fourierᴴ =
      permutation (sumGate target control (-weight) (Ne.symm h)).toEquiv := by
  have hi : fourier * permutation (sumGate control target weight h).toEquiv =
      permutation (sumGate target control (-weight) (Ne.symm h)).toEquiv * fourier := by
    apply fourier_linear_intertwine
    intro i j
    change i ⬝ᵥ (sumMatrix control target weight *ᵥ j) =
      (sumMatrix target control (- -weight) *ᵥ i) ⬝ᵥ j
    rw [neg_neg, ← sumMatrix_transpose, dotProduct_comm (_ *ᵥ i) j,
      Matrix.dotProduct_transpose_mulVec]
  rw [hi, Matrix.mul_assoc, fourier_mul_adjoint, Matrix.mul_one]

/-- The same Fourier commutes exactly with a SWAP, in every characteristic. -/
theorem fourier_conjugate_SWAP (g : Circuit.SWAP ι) :
    fourier * permutation (swapGate g (p := p)).toEquiv * fourierᴴ =
      permutation (swapGate g (p := p)).toEquiv := by
  have hi : fourier * permutation (swapGate g (p := p)).toEquiv =
      permutation (swapGate g (p := p)).toEquiv * fourier := by
    apply fourier_linear_intertwine
    intro i j
    exact swapGate_pairing g i j
  rw [hi, Matrix.mul_assoc, fourier_mul_adjoint, Matrix.mul_one]

/-- Fourier sends the normalized |0⟩ ancilla state to the normalized |+⟩ state. -/
theorem fourier_zeroState : fourier *ᵥ (zeroState : State p ι) = plusState := by
  funext s
  simp [zeroState, ket, Matrix.mulVec, dotProduct, fourier, Pi.single_apply,
    fourierScale, plusState]

/-- The reverse ancilla exchange is also exact, without a phase. -/
theorem fourier_plusState : fourier *ᵥ (plusState : State p ι) = zeroState := by
  funext s
  change (∑ t : Config p ι,
      (fourierScale (p := p) (ι := ι) * phase (s ⬝ᵥ t)) *
        fourierScale (p := p) (ι := ι)) = _
  have h : (∑ t : Config p ι,
      (fourierScale (p := p) (ι := ι) * phase (s ⬝ᵥ t)) *
        fourierScale (p := p) (ι := ι)) =
      (fourierScale (p := p) (ι := ι) * fourierScale (p := p) (ι := ι)) *
        ∑ t : Config p ι, phase (s ⬝ᵥ t) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [h, character_sum]
  by_cases hs : s = 0
  · subst s
    simpa [zeroState, ket] using (fourierScale_square_card (p := p) (ι := ι))
  · simp [hs, zeroState, ket]

end Decoupling.HighDim.PauliUnitary

namespace Decoupling.HighDim.Circuit

variable {K : Type*} [CommRing K] {D : ℕ} {ι : Type*}
  [Fintype ι] [DecidableEq ι]

/-- Fourier conjugation stays within the actual SUM/SWAP gate alphabet.
For SUM it reverses the sites and negates the weight; SWAP is unchanged. -/
def fourierDual : Layer K D ι → Layer K D ι
  | .sum g => .sum g.dual
  | .swap g => .swap g

omit [Fintype ι] in
theorem fourierDual_xMatrix (g : Layer K D ι) : (fourierDual g).xMatrix = g.zMatrix := by
  cases g with
  | sum g => exact g.dual_xMatrix
  | swap g => rfl

omit [Fintype ι] in
theorem fourierDual_zMatrix (g : Layer K D ι) : (fourierDual g).zMatrix = g.xMatrix := by
  cases g with
  | sum g => exact g.dual_zMatrix
  | swap g => rfl

theorem wordX_fourierDual (c : List (Layer K D ι)) :
    wordX (c.map fourierDual) = wordZ c := by
  induction c with
  | nil => simp
  | cons g c ih => simp [fourierDual_xMatrix, ih]

theorem wordZ_fourierDual (c : List (Layer K D ι)) :
    wordZ (c.map fourierDual) = wordX c := by
  induction c with
  | nil => simp
  | cons g c ih => simp [fourierDual_zMatrix, ih]

omit [Fintype ι] [DecidableEq ι] in
theorem fourierDual_SUM_sites (g : SUM K D ι) (n : Translation D) :
    g.dual.source (n + g.displacement) = g.destination n ∧
    g.dual.destination (n + g.displacement) = g.source n := by
  simp [SUM.dual, SUM.source, SUM.destination]

omit [Fintype ι] [DecidableEq ι] in
theorem fourierDual_range (c : List (Layer K D ι)) :
    wordRangeBound (c.map fourierDual) = wordRangeBound c := by
  induction c with
  | nil => rfl
  | cons g c ih =>
    cases g <;> simp_all [wordRangeBound, fourierDual, Layer.displacement, SUM.dual]

end Decoupling.HighDim.Circuit
