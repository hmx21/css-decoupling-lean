import Decoupling.HighDim.LaurentBoxesOperations
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# HD012 actual scalar systems for linear equations in unknown matrices

The coefficients below are explicit products of known matrix entries.
Flattening is proved to preserve the original matrix equation exactly.
This is used for cochain-map, contraction and projective-lift equations;
it asserts no solvability or cost bound for an unspecified solver.
-/
namespace Decoupling.HighDim.MatrixLinearSystems
open Matrix
noncomputable section

variable {R : Type*} [CommRing R]
  {I A B C E : Type*} [Fintype I] [Fintype B] [Fintype C]

/-- Coefficients of the actual map `X ↦ ∑ k, L k * X * R k`. -/
def coefficients (L : I → Matrix A B R) (P : I → Matrix C E R) :
    Matrix (A × E) (B × C) R :=
  fun ij ab => ∑ k, L k ij.1 ab.1 * P k ab.2 ij.2

theorem coefficients_mulVec (L : I → Matrix A B R) (P : I → Matrix C E R)
    (X : Matrix B C R) :
    coefficients L P *ᵥ (fun ab => X ab.1 ab.2) =
      fun ij => (∑ k, L k * X * P k) ij.1 ij.2 := by
  classical
  funext ij
  simp only [coefficients, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.sum_apply, Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset B)) (t := (Finset.univ : Finset I))]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem equation_iff (L : I → Matrix A B R) (P : I → Matrix C E R)
    (X : Matrix B C R) (Y : Matrix A E R) :
    (∑ k, L k * X * P k) = Y ↔
      coefficients L P *ᵥ (fun ab => X ab.1 ab.2) = fun ij => Y ij.1 ij.2 := by
  rw [coefficients_mulVec]
  constructor
  · intro h
    rw [h]
  · intro h
    funext i j
    exact congrFun h (i,j)

/-- Every genuine solution of the scalar system reconstructs a matrix
solution, including rectangular or empty matrices. -/
theorem solvable_iff (L : I → Matrix A B R) (P : I → Matrix C E R)
    (Y : Matrix A E R) :
    (∃ X : Matrix B C R, (∑ k, L k * X * P k) = Y) ↔
      ∃ x : B × C → R, coefficients L P *ᵥ x = fun ij => Y ij.1 ij.2 := by
  constructor
  · rintro ⟨X, hX⟩
    exact ⟨fun ab => X ab.1 ab.2, (equation_iff L P X Y).mp hX⟩
  · rintro ⟨x, hx⟩
    exact ⟨fun b c => x (b,c), (equation_iff L P _ Y).mpr hx⟩

variable {K : Type*} [CommRing K] {D a b : ℕ}

omit [Fintype B] [Fintype C] in
/-- Actual coefficient-box bound, rather than an assumed system-size
certificate. The number of summands does not enlarge exponent support. -/
theorem coefficients_supported (L : I → Matrix A B (Laurent K D))
    (P : I → Matrix C E (Laurent K D))
    (hL : ∀ k, LaurentBoxes.MatrixSupported (L k) a)
    (hP : ∀ k, LaurentBoxes.MatrixSupported (P k) b) :
    LaurentBoxes.MatrixSupported (coefficients L P) (a + b) := by
  intro ij ab
  apply LaurentBoxes.supported_sum
  intro k _
  exact LaurentBoxes.supported_mul (hL k ij.1 ab.1) (hP k ab.2 ij.2)

end
end Decoupling.HighDim.MatrixLinearSystems
