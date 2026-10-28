import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.CharP.Two
import Mathlib.LinearAlgebra.Pi
import Mathlib.Tactic.Ring
import Decoupling.Laurent

/-!
# Koszul differentials and the coarse-graining comparison coefficients

The basis conventions are exactly those in `notes/main.pdf`, Eq. (13):
`K₁ = (eₓ, eᵧ, e_z)` and `K₂ = (eᵧ ∧ e_z, e_z ∧ eₓ, eₓ ∧ eᵧ)`.
The degree-zero and degree-three modules have rank one.

The comparison matrices below record **coefficients in R**. In the manuscript,
their sources are free modules over `S ⊆ R`. They do not assert that the
comparison maps are square matrices over S: scalar restriction increases the
target ranks by eight. The comparison identities are identities after embedding
the S coefficients into R, where `X - 1 = u²`, `Y - 1 = v²`, `Z - 1 = w²`.

This file proves the chain identities and the vanishing of the degree-two
composite with an R-linear map into an annihilated module. It does not prove
exactness of the Koszul complex, regularity of the sequence, the Yoneda
comparison theorem, or the full Ext restriction/splitting theorem.
-/

namespace Decoupling.Koszul

open Matrix

variable {R : Type*} [CommRing R]

/-- `∂₁`, with columns ordered `x,y,z`. -/
def d₁ (u v w : R) : Matrix (Fin 1) (Fin 3) R := !![u, v, w]

/-- `∂₂`, with rows `x,y,z` and columns `yz,zx,xy`. -/
def d₂ (u v w : R) : Matrix (Fin 3) (Fin 3) R :=
  !![0, w, v; w, 0, u; v, u, 0]

/-- `∂₃`, with rows ordered `yz,zx,xy`. -/
def d₃ (u v w : R) : Matrix (Fin 3) (Fin 1) R := !![u; v; w]

section CharacteristicTwo

variable [CharP R 2]

/-- Consecutive Koszul differentials compose to zero, Eq. (13). -/
theorem d₁_mul_d₂ (u v w : R) : d₁ u v w * d₂ u v w = 0 := by
  ext i j
  fin_cases i
  fin_cases j <;>
    simp [d₁, d₂, Matrix.mul_apply, Fin.sum_univ_succ, mul_comm,
      CharTwo.add_self_eq_zero]

/-- Consecutive Koszul differentials compose to zero, Eq. (13). -/
theorem d₂_mul_d₃ (u v w : R) : d₂ u v w * d₃ u v w = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d₂, d₃, Matrix.mul_apply, Fin.sum_univ_succ, mul_comm,
      CharTwo.add_self_eq_zero]

end CharacteristicTwo

/-- R coefficients of the degree-one comparison, Eq. (31). -/
def χ₁ (u v w : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal ![u, v, w]

/-- R coefficients of the degree-two comparison, in order `yz,zx,xy`. -/
def χ₂ (u v w : R) : Matrix (Fin 3) (Fin 3) R :=
  Matrix.diagonal ![v * w, w * u, u * v]

/-- R coefficient of the degree-three comparison. -/
def χ₃ (u v w : R) : Matrix (Fin 1) (Fin 1) R := !![u * v * w]

/-- The degree-one comparison identity, with S coefficients embedded into R. -/
theorem d₁_mul_χ₁ (u v w : R) :
    d₁ u v w * χ₁ u v w = d₁ (u ^ 2) (v ^ 2) (w ^ 2) := by
  ext i j
  fin_cases i
  fin_cases j <;>
    simp [d₁, χ₁, Matrix.mul_apply, Fin.sum_univ_succ, pow_two]

/-- The degree-two comparison identity, Eq. (32), in R coefficients. -/
theorem d₂_mul_χ₂ (u v w : R) :
    d₂ u v w * χ₂ u v w = χ₁ u v w * d₂ (u ^ 2) (v ^ 2) (w ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d₂, χ₁, χ₂, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The degree-three comparison identity, Eq. (32), in R coefficients. -/
theorem d₃_mul_χ₃ (u v w : R) :
    d₃ u v w * χ₃ u v w = χ₂ u v w * d₃ (u ^ 2) (v ^ 2) (w ^ 2) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d₃, χ₂, χ₃, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The explicit degree-two product displayed in Eq. (32). -/
theorem d₂_mul_χ₂_explicit (u v w : R) :
    d₂ u v w * χ₂ u v w =
      !![0, u * w ^ 2, u * v ^ 2;
         v * w ^ 2, 0, u ^ 2 * v;
         v ^ 2 * w, u ^ 2 * w, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d₂, χ₂, Matrix.mul_apply, Fin.sum_univ_succ] <;> ring

/-- The explicit degree-three product displayed in Eq. (32). -/
theorem d₃_mul_χ₃_explicit (u v w : R) :
    d₃ u v w * χ₃ u v w =
      !![u ^ 2 * v * w; u * v ^ 2 * w; u * v * w ^ 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [d₃, χ₃, Matrix.mul_apply] <;> ring

section CoefficientEmbedding

variable (S : Type*) [CommRing S] [Algebra S R]

/-- A diagonal coefficient formula with its genuine S-linear source and target.
No claim of injectivity or freeness of `R` over `S` is built into this map. -/
def diagonalOver {ι : Type*} (c : ι → R) : (ι → S) →ₗ[S] (ι → R) where
  toFun a i := c i * algebraMap S R (a i)
  map_add' a b := by
    ext i
    simp [mul_add]
  map_smul' s a := by
    ext i
    simp [Algebra.smul_def, mul_left_comm]

/-- The degree-zero coefficient inclusion, as an S-linear map. -/
def χ₀Over : (Fin 1 → S) →ₗ[S] (Fin 1 → R) :=
  diagonalOver S (fun _ => 1)

/-- The actual degree-one comparison has source `S³` and target `R³`. -/
def χ₁Over (u v w : R) : (Fin 3 → S) →ₗ[S] (Fin 3 → R) :=
  diagonalOver S ![u, v, w]

/-- The actual degree-two comparison has source `S³` and target `R³`. -/
def χ₂Over (u v w : R) : (Fin 3 → S) →ₗ[S] (Fin 3 → R) :=
  diagonalOver S ![v * w, w * u, u * v]

/-- The actual degree-three comparison has source `S` and target `R`. -/
def χ₃Over (u v w : R) : (Fin 1 → S) →ₗ[S] (Fin 1 → R) :=
  diagonalOver S ![u * v * w]

variable (u v w : R) (U V W : S)
  (hU : algebraMap S R U = u ^ 2)
  (hV : algebraMap S R V = v ^ 2)
  (hW : algebraMap S R W = w ^ 2)

include hU hV hW

/-- The degree-one square commutes on S-valued inputs. In the manuscript,
`U = X - 1`, `V = Y - 1`, and `W = Z - 1`. -/
theorem comparison₁_over (a : Fin 3 → S) :
    d₁ u v w *ᵥ χ₁Over S u v w a = χ₀Over S (d₁ U V W *ᵥ a) := by
  ext i
  fin_cases i
  simp [χ₁Over, χ₀Over, diagonalOver, d₁, Matrix.mulVec, dotProduct,
    Fin.sum_univ_succ, hU, hV, hW]
  ring

/-- The degree-two comparison identity with actual S-linear domains. -/
theorem comparison₂_over (a : Fin 3 → S) :
    d₂ u v w *ᵥ χ₂Over S u v w a =
      χ₁Over S u v w (d₂ U V W *ᵥ a) := by
  ext i
  fin_cases i <;>
    simp [χ₂Over, χ₁Over, diagonalOver, d₂, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, hU, hV, hW] <;> ring

/-- The degree-three comparison identity with actual S-linear domains. -/
theorem comparison₃_over (a : Fin 1 → S) :
    d₃ u v w *ᵥ χ₃Over S u v w a =
      χ₂Over S u v w (d₃ U V W *ᵥ a) := by
  ext i
  fin_cases i <;>
    simp [χ₃Over, χ₂Over, diagonalOver, d₃, Matrix.mulVec, dotProduct,
      hU, hV, hW] <;> ring

end CoefficientEmbedding

section AnnihilatedTarget

variable {M E : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup E] [Module R E]

/-- The degree-two comparison on three blocks. With `M = Fin t₂ → R`, this
is exactly the manuscript's `χ₂ = diag(vw I, wu I, uv I)` on embedded inputs. -/
def χ₂Blocks (u v w : R) (a : Fin 3 → M) : Fin 3 → M :=
  ![(v * w) • a 0, (w * u) • a 1, (u * v) • a 2]

/-- The algebraic vanishing in Eq. (34). R-linearity of `f` is essential.
This holds for all R-valued inputs, hence also for embedded S-valued inputs.
It is not by itself a theorem about Ext restriction. -/
theorem map_χ₂Blocks_eq_zero (u v w : R) (f : (Fin 3 → M) →ₗ[R] E)
    (hu : ∀ e : E, u • e = 0) (hv : ∀ e : E, v • e = 0)
    (hw : ∀ e : E, w • e = 0) (a : Fin 3 → M) :
    f (χ₂Blocks u v w a) = 0 := by
  have h : χ₂Blocks u v w a =
      v • ![w • a 0, 0, 0] + w • ![0, u • a 1, 0] +
        u • ![0, 0, v • a 2] := by
    ext i
    fin_cases i <;> simp [χ₂Blocks, mul_smul]
  rw [h, map_add, map_add, map_smul, map_smul, map_smul, hv, hw, hu]
  simp

/-- Agreement between the block description and the one-copy matrix. -/
theorem χ₂_mulVec (u v w : R) (a : Fin 3 → R) :
    χ₂ u v w *ᵥ a = χ₂Blocks u v w a := by
  ext i
  fin_cases i <;> simp [χ₂, χ₂Blocks, Matrix.mulVec_diagonal]

/-- One-copy version of the vanishing statement, written with the matrix. -/
theorem map_χ₂_mulVec_eq_zero (u v w : R) (f : (Fin 3 → R) →ₗ[R] E)
    (hu : ∀ e : E, u • e = 0) (hv : ∀ e : E, v • e = 0)
    (hw : ∀ e : E, w • e = 0) (a : Fin 3 → R) :
    f (χ₂ u v w *ᵥ a) = 0 := by
  rw [χ₂_mulVec]
  exact map_χ₂Blocks_eq_zero u v w f hu hv hw a

/-- The zero degree-two composite on its actual S-valued domain. The input
map is S-linear, whereas the map out is required to be originally R-linear. -/
theorem map_χ₂Over_eq_zero {S : Type*} [CommRing S] [Algebra S R]
    (u v w : R) (f : (Fin 3 → R) →ₗ[R] E)
    (hu : ∀ e : E, u • e = 0) (hv : ∀ e : E, v • e = 0)
    (hw : ∀ e : E, w • e = 0) (a : Fin 3 → S) :
    f (χ₂Over S u v w a) = 0 := by
  have h : χ₂Over S u v w a = χ₂Blocks u v w (fun i => algebraMap S R (a i)) := by
    ext i
    fin_cases i <;> simp [χ₂Over, diagonalOver, χ₂Blocks]
  rw [h]
  exact map_χ₂Blocks_eq_zero u v w f hu hv hw _

end AnnihilatedTarget

end Decoupling.Koszul

namespace Decoupling.PhysicalKoszul

noncomputable section

/-- The manuscript's `∂₁` over the actual three-variable Laurent ring. -/
abbrev partial₁ : Matrix (Fin 1) (Fin 3) R := Koszul.d₁ u v w

/-- The manuscript's `∂₂` in the ordered basis `yz,zx,xy`. -/
abbrev partial₂ : Matrix (Fin 3) (Fin 3) R := Koszul.d₂ u v w

/-- The manuscript's `∂₃` over the actual three-variable Laurent ring. -/
abbrev partial₃ : Matrix (Fin 3) (Fin 1) R := Koszul.d₃ u v w

theorem partial₁_mul_partial₂ : partial₁ * partial₂ = 0 :=
  Koszul.d₁_mul_d₂ u v w

theorem partial₂_mul_partial₃ : partial₂ * partial₃ = 0 :=
  Koszul.d₂_mul_d₃ u v w

end

end Decoupling.PhysicalKoszul
