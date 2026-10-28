import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Signed stabilization of comparison maps

This module formalizes the matrix calculation in `drafts/main.tex`,
Sections IV.B--C (`subsec:comparison` and the displayed shear factorization
in `subsec:circuit`). Rows are outputs and columns are inputs. All signs
are retained, over an arbitrary commutative ring and arbitrary finite
index types, including empty types.

`ComparisonData` records exactly the four displayed comparison identities.
This is a conditional algebraic construction: it does not assert the
existence of those data from a cokernel or derived-profile isomorphism,
nor does matrix factorization assert physical circuit realization.
-/

namespace Decoupling.HighDim.Stabilization

open Matrix

variable {R : Type*} [CommRing R]

section Theta

variable {A B : Type*} [Fintype A] [Fintype B]
  [DecidableEq A] [DecidableEq B]

/-- The paper's `Θ(f,g) : A ⊕ B → B ⊕ A`. -/
def theta (f : Matrix B A R) (g : Matrix A B R) : Matrix (B ⊕ A) (A ⊕ B) R :=
  fromBlocks f (1 - f * g) 1 (-g)

/-- The reverse construction is a right inverse, without any hypothesis
that `f` or `g` is invertible. -/
theorem theta_mul_reverse (f : Matrix B A R) (g : Matrix A B R) :
    theta f g * theta g f = 1 := by
  simp [theta, fromBlocks_multiply, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_assoc, fromBlocks_one]

/-- Both inverse identities. The sum types need not be nonempty. -/
theorem theta_inverse (f : Matrix B A R) (g : Matrix A B R) :
    theta f g * theta g f = 1 ∧ theta g f * theta f g = 1 :=
  ⟨theta_mul_reverse f g, theta_mul_reverse g f⟩

/-- Two signed shears and an on-site summand permutation, rightmost first. -/
theorem theta_factorization (f : Matrix B A R) (g : Matrix A B R) :
    theta f g =
      fromBlocks (1 : Matrix B B R) f 0 (1 : Matrix A A R) *
      fromBlocks (1 : Matrix B B R) 0 (-g) (1 : Matrix A A R) *
      fromBlocks (0 : Matrix B A R) (1 : Matrix B B R)
        (1 : Matrix A A R) 0 := by
  simp [theta, fromBlocks_multiply, sub_eq_add_neg]

end Theta

variable (R) (C₀ C₁ T₀ T₁ : Type*)
  [Fintype C₀] [Fintype C₁] [Fintype T₀] [Fintype T₁]
  [DecidableEq C₀] [DecidableEq C₁] [DecidableEq T₀] [DecidableEq T₁]

/-- Conditional input for the stabilization construction, in the exact
degrees and signs of the paper. No existence result is encoded here. -/
structure ComparisonData where
  dC : Matrix C₁ C₀ R
  dT : Matrix T₁ T₀ R
  phi0 : Matrix C₀ T₀ R
  psi0 : Matrix T₀ C₀ R
  phi1 : Matrix C₁ T₁ R
  psi1 : Matrix T₁ C₁ R
  etaC : Matrix C₀ C₁ R
  etaT : Matrix T₀ T₁ R
  forward : dC * phi0 = phi1 * dT
  backward : dT * psi0 = psi1 * dC
  homotopyC : dC * etaC = 1 - phi1 * psi1
  homotopyT : dT * etaT = 1 - psi1 * phi1

namespace ComparisonData

variable {R C₀ C₁ T₀ T₁}
variable (c : ComparisonData R C₀ C₁ T₀ T₁)

/-- Stabilized degree-one map `Ĉ¹ → T̂¹`. -/
def V : Matrix (T₁ ⊕ C₁) (C₁ ⊕ T₁) R := theta c.psi1 c.phi1

/-- Explicit inverse of the stabilized degree-one map. -/
def VInv : Matrix (C₁ ⊕ T₁) (T₁ ⊕ C₁) R := theta c.phi1 c.psi1

omit [DecidableEq C₀] [DecidableEq T₀] in
theorem V_inverse : c.V * c.VInv = 1 ∧ c.VInv * c.V = 1 :=
  theta_inverse c.psi1 c.phi1

/-- The differential after adjoining `D⁰(T¹)`. -/
def dCPrime : Matrix (C₁ ⊕ T₁) (C₀ ⊕ T₁) R := fromBlocks c.dC 0 0 1

/-- The differential after adjoining `D⁰(C¹)`. -/
def dTPrime : Matrix (T₁ ⊕ C₁) (T₀ ⊕ C₁) R := fromBlocks c.dT 0 0 1

/-- The enlarged lift `φ̂⁰`, with its essential negative `ψ¹` block. -/
def phiHat : Matrix (C₀ ⊕ T₁) (T₀ ⊕ C₁) R :=
  fromBlocks c.phi0 c.etaC c.dT (-c.psi1)

/-- The enlarged lift `ψ̂⁰`, with its essential negative `φ¹` block. -/
def psiHat : Matrix (T₀ ⊕ C₁) (C₀ ⊕ T₁) R :=
  fromBlocks c.psi0 c.etaT c.dC (-c.phi1)

omit [DecidableEq C₀] [DecidableEq T₀] in
/-- First enlarged comparison identity: `d'_C φ̂⁰ = V⁻¹ d'_T`. -/
theorem dCPrime_phiHat : c.dCPrime * c.phiHat = c.VInv * c.dTPrime := by
  simp [dCPrime, phiHat, VInv, dTPrime, theta, fromBlocks_multiply,
    c.forward, c.homotopyC]

omit [DecidableEq C₀] [DecidableEq T₀] in
/-- Second enlarged comparison identity: `d'_T ψ̂⁰ = V d'_C`. -/
theorem dTPrime_psiHat : c.dTPrime * c.psiHat = c.V * c.dCPrime := by
  simp [dTPrime, psiHat, V, dCPrime, theta, fromBlocks_multiply,
    c.backward, c.homotopyT]

/-- Stabilized degree-zero map `Ĉ⁰ → T̂⁰`. -/
def U : Matrix ((T₀ ⊕ C₁) ⊕ (C₀ ⊕ T₁)) ((C₀ ⊕ T₁) ⊕ (T₀ ⊕ C₁)) R :=
  theta c.psiHat c.phiHat

/-- Explicit inverse of the stabilized degree-zero map. -/
def UInv : Matrix ((C₀ ⊕ T₁) ⊕ (T₀ ⊕ C₁)) ((T₀ ⊕ C₁) ⊕ (C₀ ⊕ T₁)) R :=
  theta c.phiHat c.psiHat

theorem U_inverse : c.U * c.UInv = 1 ∧ c.UInv * c.U = 1 :=
  theta_inverse c.psiHat c.phiHat

omit [DecidableEq C₀] [DecidableEq T₀] in
/-- The two enlarged lifts need not be inverses, but their composite
induces the identity after applying `d'_T`. -/
theorem dTPrime_psiHat_phiHat : c.dTPrime * c.psiHat * c.phiHat = c.dTPrime := by
  rw [c.dTPrime_psiHat, Matrix.mul_assoc, c.dCPrime_phiHat, ← Matrix.mul_assoc,
    c.V_inverse.1, Matrix.one_mul]

omit [DecidableEq C₀] [DecidableEq T₀] in
/-- The second block column of the stabilized square vanishes, with subtraction. -/
theorem second_column_zero :
    c.dTPrime - c.dTPrime * c.psiHat * c.phiHat = 0 := by
  rw [c.dTPrime_psiHat_phiHat, sub_self]

/-- Differential of `Ĉ` in the paper's displayed order of summands. -/
def dCHat : Matrix (C₁ ⊕ T₁) ((C₀ ⊕ T₁) ⊕ (T₀ ⊕ C₁)) R :=
  Matrix.fromCols c.dCPrime 0

/-- Differential of `T̂` in the paper's displayed order of summands. -/
def dTHat : Matrix (T₁ ⊕ C₁) ((T₀ ⊕ C₁) ⊕ (C₀ ⊕ T₁)) R :=
  Matrix.fromCols c.dTPrime 0

/-- The stabilized commuting square `d̂_T U = V d̂_C`. This is a
matrix statement conditional on `ComparisonData`, not the decoupling theorem. -/
theorem stabilized_square : c.dTHat * c.U = c.V * c.dCHat := by
  simp only [dTHat, dCHat, U, theta, Matrix.fromCols_mul_fromBlocks,
    Matrix.mul_fromCols, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  rw [c.dTPrime_psiHat, Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc,
    c.second_column_zero]

/-- The same explicit two-shear factorization for the final qudit matrix. -/
theorem U_factorization :
    c.U =
      fromBlocks (1 : Matrix (T₀ ⊕ C₁) (T₀ ⊕ C₁) R) c.psiHat 0
        (1 : Matrix (C₀ ⊕ T₁) (C₀ ⊕ T₁) R) *
      fromBlocks (1 : Matrix (T₀ ⊕ C₁) (T₀ ⊕ C₁) R) 0 (-c.phiHat)
        (1 : Matrix (C₀ ⊕ T₁) (C₀ ⊕ T₁) R) *
      fromBlocks (0 : Matrix (T₀ ⊕ C₁) (C₀ ⊕ T₁) R)
        (1 : Matrix (T₀ ⊕ C₁) (T₀ ⊕ C₁) R)
        (1 : Matrix (C₀ ⊕ T₁) (C₀ ⊕ T₁) R) 0 :=
  theta_factorization c.psiHat c.phiHat

end ComparisonData

end Decoupling.HighDim.Stabilization
