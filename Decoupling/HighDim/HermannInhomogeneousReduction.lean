import Decoupling.HighDim.HermannMatrixReduction

/-!
# Actual inhomogeneous Hermann reduction

A constructed right-inverse-up-to-δ matrix H satisfies A H = δ I, and
E = δ I - H A is the actual syzygy matrix. First divide the right side by
δ and remove H times the quotient. Then apply all-coordinate reduction.
This proves the remaining smaller equation has a small-last-degree solution;
no such solution is assumed. Any solution of it is explicitly lifted back.
-/

namespace Decoupling.HighDim.Hermann
open Polynomial Matrix
noncomputable section
variable {R : Type*} [CommRing R] {m n : ℕ}

def rhsQuotient (δ : R[X]) (b : Fin m → R[X]) := fun i => b i /ₘ δ

def rhsRemainder (δ : R[X]) (b : Fin m → R[X]) := fun i => b i %ₘ δ

def inhomogeneousLift (δ : R[X]) (H : Matrix (Fin n) (Fin m) R[X]) (b : Fin m → R[X]) :=
  H *ᵥ rhsQuotient δ b

/-- Removing the explicit lift leaves the actual remainder of the right side. -/
theorem equation_sub_lift (δ : R[X]) (A : Matrix (Fin m) (Fin n) R[X])
    (H : Matrix (Fin n) (Fin m) R[X]) (hAH : A * H = δ • 1)
    (b : Fin m → R[X]) (y : Fin n → R[X]) (hy : A *ᵥ y = b) :
    A *ᵥ (y - inhomogeneousLift δ H b) = rhsRemainder δ b := by
  rw [inhomogeneousLift, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hAH,
    Matrix.smul_mulVec, Matrix.one_mulVec, hy]
  funext i
  exact (Polynomial.modByMonic_eq_sub_mul_div (b i) δ).symm

/-- Every solution of the reduced right side yields an actual original solution. -/
theorem equation_add_lift (δ : R[X]) (A : Matrix (Fin m) (Fin n) R[X])
    (H : Matrix (Fin n) (Fin m) R[X]) (hAH : A * H = δ • 1)
    (b : Fin m → R[X]) (z : Fin n → R[X]) (hz : A *ᵥ z = rhsRemainder δ b) :
    A *ᵥ (z + inhomogeneousLift δ H b) = b := by
  rw [inhomogeneousLift, Matrix.mulVec_add, Matrix.mulVec_mulVec, hAH,
    Matrix.smul_mulVec, Matrix.one_mulVec, hz]
  funext i
  exact Polynomial.modByMonic_add_div (b i) δ

/-- The actual correction matrix has zero composite with A. -/
theorem mul_correction_eq_zero (δ : R[X]) (A : Matrix (Fin m) (Fin n) R[X])
    (H : Matrix (Fin n) (Fin m) R[X]) (hAH : A * H = δ • 1) :
    A * (δ • 1 - H * A) = 0 := by
  rw [Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one, ← Matrix.mul_assoc,
    hAH, Matrix.smul_mul, Matrix.one_mul, sub_self]

/-- This identity controls the remainder even though it solves a nonzero equation. -/
theorem scalar_matrixRemainder_inhomogeneous (δ : R[X])
    (A : Matrix (Fin m) (Fin n) R[X]) (H : Matrix (Fin n) (Fin m) R[X])
    (E : Matrix (Fin n) (Fin n) R[X]) (hE : E = δ • 1 - H * A)
    (g : Fin m → R[X]) (y : Fin n → R[X]) (hy : A *ᵥ y = g) :
    δ • matrixRemainder δ E y =
      E *ᵥ (fun j => y j %ₘ δ) + H *ᵥ g := by
  have hEy : E *ᵥ y = δ • y - H *ᵥ g := by
    rw [hE, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      ← Matrix.mulVec_mulVec, hy]
  have hyy : δ • y = E *ᵥ y + H *ᵥ g := by rw [hEy]; abel
  have hrem : (fun j => y j %ₘ δ) = y - δ • (fun j => y j /ₘ δ) := by
    funext j
    exact Polynomial.modByMonic_eq_sub_mul_div (y j) δ
  rw [matrixRemainder, smul_sub, hyy, ← Matrix.mulVec_smul, hrem, Matrix.mulVec_sub]
  abel

variable [IsDomain R]

/-- A strict last-variable bound for the actual inhomogeneous remainder. -/
theorem matrixRemainder_inhomogeneous_degree (δ : R[X]) (hδ : δ.Monic)
    (A : Matrix (Fin m) (Fin n) R[X]) (H : Matrix (Fin n) (Fin m) R[X])
    (E : Matrix (Fin n) (Fin n) R[X]) (hE : E = δ • 1 - H * A)
    (M : ℕ) (hdegE : ∀ i j, (E i j).natDegree ≤ M)
    (hdegH : ∀ i j, (H i j).natDegree ≤ M)
    (b : Fin m → R[X]) (y : Fin n → R[X])
    (hy : A *ᵥ y = rhsRemainder δ b) (i : Fin n) :
    (matrixRemainder δ E y i).degree < (M : WithBot ℕ) := by
  have heq := scalar_matrixRemainder_inhomogeneous δ A H E hE _ y hy
  by_cases hδ1 : δ = 1
  · have hz : matrixRemainder δ E y = 0 := by
      have hz₁ : (fun j => y j %ₘ δ) = (0 : Fin n → R[X]) := by funext j; simp [hδ1]
      have hz₂ : rhsRemainder δ b = 0 := by funext j; simp [rhsRemainder, hδ1]
      rw [hz₁, hz₂, Matrix.mulVec_zero, Matrix.mulVec_zero, add_zero,
        hδ1, one_smul] at heq
      simpa only [hδ1] using heq
    simp [hz]
  · by_cases hz : matrixRemainder δ E y i = 0
    · simp [hz]
    have hsumE : ((E *ᵥ (fun j => y j %ₘ δ)) i).natDegree ≤ M + (δ.natDegree - 1) := by
      change (∑ j, E i j * (y j %ₘ δ)).natDegree ≤ _
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j _
      exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hdegE i j)
        (Nat.le_sub_one_of_lt (Polynomial.natDegree_modByMonic_lt _ hδ hδ1)))
    have hsumH : ((H *ᵥ rhsRemainder δ b) i).natDegree ≤ M + (δ.natDegree - 1) := by
      change (∑ j, H i j * (b j %ₘ δ)).natDegree ≤ _
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j _
      exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hdegH i j)
        (Nat.le_sub_one_of_lt (Polynomial.natDegree_modByMonic_lt _ hδ hδ1)))
    have hbnd := (Polynomial.natDegree_add_le _ _).trans (max_le hsumE hsumH)
    have hp : (δ * matrixRemainder δ E y i).natDegree =
        δ.natDegree + (matrixRemainder δ E y i).natDegree := Polynomial.natDegree_mul hδ.ne_zero hz
    have hh := congrArg Polynomial.natDegree (congrFun heq i)
    change (δ * matrixRemainder δ E y i).natDegree =
      ((E *ᵥ (fun j => y j %ₘ δ)) i + (H *ᵥ rhsRemainder δ b) i).natDegree at hh
    rw [hp] at hh
    have hpos : 0 < δ.natDegree := hδ.natDegree_pos.mpr hδ1
    apply (Polynomial.natDegree_lt_iff_degree_lt hz).mp
    omega

/-- A solvable equation has a genuine reduced solution with the strict
last-variable cutoff. The original right side is recovered by equation_add_lift. -/
theorem exists_reduced_inhomogeneous_solution (δ : R[X]) (hδ : δ.Monic)
    (A : Matrix (Fin m) (Fin n) R[X]) (H : Matrix (Fin n) (Fin m) R[X])
    (E : Matrix (Fin n) (Fin n) R[X]) (hAH : A * H = δ • 1)
    (hE : E = δ • 1 - H * A) (M : ℕ)
    (hdegE : ∀ i j, (E i j).natDegree ≤ M) (hdegH : ∀ i j, (H i j).natDegree ≤ M)
    (b : Fin m → R[X]) (hsol : ∃ y, A *ᵥ y = b) :
    ∃ z, A *ᵥ z = rhsRemainder δ b ∧ ∀ i, (z i).degree < (M : WithBot ℕ) := by
  obtain ⟨y, hy⟩ := hsol
  let y₀ := y - inhomogeneousLift δ H b
  have h₀ : A *ᵥ y₀ = rhsRemainder δ b := equation_sub_lift δ A H hAH b y hy
  have hAE : A * E = 0 := by rw [hE]; exact mul_correction_eq_zero δ A H hAH
  refine ⟨matrixRemainder δ E y₀, ?_,
    matrixRemainder_inhomogeneous_degree δ hδ A H E hE M hdegE hdegH b y₀ h₀⟩
  rw [matrixRemainder, Matrix.mulVec_sub, Matrix.mulVec_mulVec, hAE,
    Matrix.zero_mulVec, sub_zero, h₀]

end
end Decoupling.HighDim.Hermann
