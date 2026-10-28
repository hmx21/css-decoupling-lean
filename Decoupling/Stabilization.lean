import Mathlib.Data.Matrix.Block
import Mathlib.Data.Matrix.ColumnRowPartitioned
import Mathlib.Algebra.CharP.Two

/-!
# The stabilization construction in main.pdf, Section IV

Rows are target coordinates; columns are source coordinates. `block f g`
is the paper's 𝒮(f,g) : U ⊕ V → V ⊕ U, with f : V → U and g : U → V.
The characteristic-two hypothesis is essential for these plus signs.
No exactness, Ext vanishing, or existence of comparison data is assumed
implicitly: the four equations (48) are fields of `ComparisonData`.
-/

namespace Decoupling
namespace Stabilization

open Matrix

variable {A : Type*} [CommRing A] [CharP A 2]

@[simp] theorem matrix_add_self {m n : Type*} (M : Matrix m n A) : M + M = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero _

@[simp] theorem matrix_add_cancel_left {m n : Type*} (M N : Matrix m n A) :
    M + (M + N) = N := by rw [← add_assoc, matrix_add_self, zero_add]

@[simp] theorem matrix_add_cancel_right {m n : Type*} (M N : Matrix m n A) :
    M + N + N = M := by rw [add_assoc, matrix_add_self, add_zero]

section Block
variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

/-- Equation (54), including the order of the source and target summands. -/
def block (f : Matrix U V A) (g : Matrix V U A) : Matrix (V ⊕ U) (U ⊕ V) A :=
  fromBlocks g (1 + g * f) 1 f

/-- Lemma IV.1: one of the two inverse identities; swapping f,g gives the other. -/
theorem block_mul_reverse (f : Matrix U V A) (g : Matrix V U A) :
    block f g * block g f = 1 := by
  simp [block, fromBlocks_multiply, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc,
    add_left_comm, add_comm, fromBlocks_one]

/-- Both inverse identities, valid also when either index type is empty. -/
theorem block_inverse (f : Matrix U V A) (g : Matrix V U A) :
    block f g * block g f = 1 ∧ block g f * block f g = 1 :=
  ⟨block_mul_reverse f g, block_mul_reverse g f⟩

omit [CharP A 2] in
/-- Equation (67): two shears and the summand permutation, rightmost first. -/
theorem block_factorization (f : Matrix U V A) (g : Matrix V U A) :
    block f g =
      fromBlocks (1 : Matrix V V A) g 0 (1 : Matrix U U A) *
      fromBlocks (1 : Matrix V V A) 0 f (1 : Matrix U U A) *
      fromBlocks (0 : Matrix V U A) (1 : Matrix V V A) (1 : Matrix U U A) 0 := by
  simp [block, fromBlocks_multiply]

end Block

variable (A) (F₀ F₁ G₀ G₁ : Type*)
  [Fintype F₀] [Fintype F₁] [Fintype G₀] [Fintype G₁]
  [DecidableEq F₀] [DecidableEq F₁] [DecidableEq G₀] [DecidableEq G₁]

/-- Precisely the four comparison identities in equation (48). -/
structure ComparisonData where
  d₁ : Matrix F₀ F₁ A
  td₁ : Matrix G₀ G₁ A
  φ₀ : Matrix F₀ G₀ A
  ρ₀ : Matrix G₀ F₀ A
  φ₁ : Matrix F₁ G₁ A
  ρ₁ : Matrix G₁ F₁ A
  η₀ : Matrix F₁ F₀ A
  tη₀ : Matrix G₁ G₀ A
  forward : d₁ * φ₁ = φ₀ * td₁
  backward : td₁ * ρ₁ = ρ₀ * d₁
  homotopyF : d₁ * η₀ = 1 + φ₀ * ρ₀
  homotopyG : td₁ * tη₀ = 1 + ρ₀ * φ₀

namespace ComparisonData

variable {A F₀ F₁ G₀ G₁}
variable (c : ComparisonData A F₀ F₁ G₀ G₁)

def Ψ₀ := block c.φ₀ c.ρ₀
def Ψ₀inv := block c.ρ₀ c.φ₀
def D_F : Matrix (F₀ ⊕ G₀) (F₁ ⊕ G₀) A := fromBlocks c.d₁ 0 0 1
def D_G : Matrix (G₀ ⊕ F₀) (G₁ ⊕ F₀) A := fromBlocks c.td₁ 0 0 1
def L₁ : Matrix (F₁ ⊕ G₀) (G₁ ⊕ F₀) A := fromBlocks c.φ₁ c.η₀ c.td₁ c.ρ₀
def M₁ : Matrix (G₁ ⊕ F₀) (F₁ ⊕ G₀) A := fromBlocks c.ρ₁ c.tη₀ c.d₁ c.φ₀

omit [CharP A 2] [DecidableEq F₁] [DecidableEq G₁] in
/-- Equation (64), first square. -/
theorem D_F_L₁ : c.D_F * c.L₁ = c.Ψ₀inv * c.D_G := by
  simp [D_F, L₁, Ψ₀inv, D_G, block, fromBlocks_multiply, c.forward, c.homotopyF]

omit [CharP A 2] [DecidableEq F₁] [DecidableEq G₁] in
/-- Equation (64), second square. -/
theorem D_G_M₁ : c.D_G * c.M₁ = c.Ψ₀ * c.D_F := by
  simp [D_G, M₁, Ψ₀, D_F, block, fromBlocks_multiply, c.backward, c.homotopyG]

def U := block c.L₁ c.M₁
def Uinv := block c.M₁ c.L₁

/-- Equation (60). -/
theorem U_inverse : c.U * c.Uinv = 1 ∧ c.Uinv * c.U = 1 :=
  block_inverse c.L₁ c.M₁

omit [DecidableEq F₁] [DecidableEq G₁] in
/-- The second block column in the physical commuting square is zero. -/
theorem second_column_zero : c.D_G + c.D_G * c.M₁ * c.L₁ = 0 := by
  rw [c.D_G_M₁, Matrix.mul_assoc, c.D_F_L₁, ← Matrix.mul_assoc]
  simp [Ψ₀, Ψ₀inv, block_mul_reverse]

/-- Stabilized X checks, with the qubit order of equation (62). -/
def H_X_hat : Matrix (F₀ ⊕ G₀) ((F₁ ⊕ G₀) ⊕ (G₁ ⊕ F₀)) A :=
  Matrix.fromCols c.D_F 0

def H_X_tilde : Matrix (G₀ ⊕ F₀) ((G₁ ⊕ F₀) ⊕ (F₁ ⊕ G₀)) A :=
  Matrix.fromCols c.D_G 0

/-- Equation (65), the stable physical commuting square. -/
theorem physical_square : c.H_X_tilde * c.U = c.Ψ₀ * c.H_X_hat := by
  simp only [H_X_tilde, H_X_hat, U, block, Matrix.fromCols_mul_fromBlocks,
    Matrix.mul_fromCols, Matrix.mul_zero, Matrix.zero_mul, add_zero]
  rw [c.D_G_M₁, Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc, c.second_column_zero]

end ComparisonData
end Stabilization
end Decoupling
