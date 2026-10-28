import Decoupling.HighDim.Laurent
import Mathlib.Algebra.MonoidAlgebra.Module
import Mathlib.LinearAlgebra.Basis.Defs

/-!
# Formal partial derivatives on the actual Laurent group algebra

The exponent is an integer, so negative powers and all characteristics
are included. This will construct the example's coarse-linear nullhomotopy
explicitly after retaining the p-th power in one direction.
-/

namespace Decoupling.HighDim

noncomputable section
variable (K : Type*) [CommRing K] {D : ℕ}

def laurentDerivative (i : Fin D) : Laurent K D →ₗ[K] Laurent K D :=
  (AddMonoidAlgebra.basis (Translation D) K).constr K
    (fun a => (a i : K) • monomial K (a - translationBasis i))

@[simp] theorem laurentDerivative_monomial (i : Fin D) (a : Translation D) :
    laurentDerivative K i (monomial K a) = (a i : K) • monomial K (a - translationBasis i) := by
  exact (AddMonoidAlgebra.basis (Translation D) K).constr_basis K _ a

@[simp] theorem laurentDerivative_one (i : Fin D) : laurentDerivative K i 1 = 0 := by
  simpa only [monomial_zero, Pi.zero_apply, Int.cast_zero, zero_smul] using
    laurentDerivative_monomial K i (0 : Translation D)

theorem laurentDerivative_monomial_mul (i : Fin D) (a : Translation D) (f : Laurent K D) :
    laurentDerivative K i (monomial K a * f) =
      monomial K a * laurentDerivative K i f +
        (a i : K) • (monomial K (a - translationBasis i) * f) := by
  induction f using AddMonoidAlgebra.induction_on with
  | of b =>
    change laurentDerivative K i (monomial K a * monomial K b) =
      monomial K a * laurentDerivative K i (monomial K b) +
        (a i : K) • (monomial K (a - translationBasis i) * monomial K b)
    simp only [monomial_mul, laurentDerivative_monomial, Pi.add_apply, Int.cast_add,
      mul_smul_comm, add_smul]
    have h₁ : a + (b - translationBasis i) = a + b - translationBasis i := by abel
    have h₂ : a - translationBasis i + b = a + b - translationBasis i := by abel
    rw [h₁, h₂, add_comm]
  | add f g hf hg => simp only [mul_add, map_add, hf, hg, smul_add]; abel
  | smul c f hf =>
    simp only [mul_smul_comm, map_smul, hf, smul_add, smul_comm c (a i : K)]

theorem laurentDerivative_coordinate_mul (i j : Fin D) (f : Laurent K D) :
    laurentDerivative K i (coordinate K j * f) =
      coordinate K j * laurentDerivative K i f + if i = j then f else 0 := by
  classical
  change laurentDerivative K i (monomial K (translationBasis j) * f) = _
  rw [laurentDerivative_monomial_mul]
  by_cases h : i = j
  · subst j
    simp [translationBasis, coordinate]
  · simp [translationBasis, h, coordinate]

theorem laurentDerivative_difference_mul (i j : Fin D) (f : Laurent K D) :
    laurentDerivative K i (difference K j * f) =
      difference K j * laurentDerivative K i f + if i = j then f else 0 := by
  rw [difference, sub_mul, one_mul, map_sub, laurentDerivative_coordinate_mul]
  simp only [sub_mul, one_mul]
  abel

end
end Decoupling.HighDim
