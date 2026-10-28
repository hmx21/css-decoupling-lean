import Decoupling.HighDim.HermannReductionSpan
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Adjugate normalization and its genuine degree estimates

An actual invertible-over-the-fraction-field square block Δ turns
`Δ u + B v = 0` into the monic-reduction normal form with δ=det Δ and
C=adj(Δ) B. The polynomial degrees of δ and every entry of C are at
most r times the original entry-degree bound. This proves the minor
part of Hermann reduction, without assuming these degree bounds.
Selection of a maximal minor from an arbitrary matrix and the total-degree
preserving monic variable change remain separate obligations.
-/

namespace Decoupling.HighDim.Hermann

open Polynomial Matrix
noncomputable section
variable {R : Type*} [CommRing R] {r n : ℕ}

/-- Determinants have degree at most the sum of the entry degree bounds. -/
theorem determinant_natDegree_le (A : Matrix (Fin r) (Fin r) R[X]) (d : ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ d) : A.det.natDegree ≤ r * d := by
  rw [Matrix.det_apply]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro s _
  have hs : (Equiv.Perm.sign s • ∏ i, A (s i) i).natDegree =
      (∏ i, A (s i) i).natDegree := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
    · simp [h]
    · simp [h, Units.neg_smul]
  rw [hs]
  apply (Polynomial.natDegree_prod_le _ _).trans
  calc
    ∑ i : Fin r, (A (s i) i).natDegree ≤ ∑ _i : Fin r, d :=
      Finset.sum_le_sum (fun i _ => hA (s i) i)
    _ = r * d := by simp

/-- Cramer's replacement determinant bounds each actual normalized coefficient. -/
theorem adjugate_mul_natDegree_le (A : Matrix (Fin r) (Fin r) R[X])
    (B : Matrix (Fin r) (Fin n) R[X]) (d : ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ d)
    (hB : ∀ i j, (B i j).natDegree ≤ d) (i : Fin r) (j : Fin n) :
    ((A.adjugate * B) i j).natDegree ≤ r * d := by
  have he : (A.adjugate * B) i j = (A.updateCol i (fun k => B k j)).det := by
    change (A.adjugate *ᵥ (fun k => B k j)) i = _
    rw [← Matrix.cramer_eq_adjugate_mulVec, Matrix.cramer_apply]
  rw [he]
  apply determinant_natDegree_le
  intro k l
  rw [Matrix.updateCol_apply]
  split
  · exact hB k j
  · exact hA k l

/-- The original polynomial system before adjugate normalization. -/
def blockMap (A : Matrix (Fin r) (Fin r) R[X]) (B : Matrix (Fin r) (Fin n) R[X]) :
    ((Fin r → R[X]) × (Fin n → R[X])) →ₗ[R[X]] (Fin r → R[X]) :=
  A.mulVecLin.coprod B.mulVecLin

/-- A literal equality of polynomial linear maps, not only equal kernel dimensions. -/
theorem normalMap_eq_adjugate (A : Matrix (Fin r) (Fin r) R[X])
    (B : Matrix (Fin r) (Fin n) R[X]) :
    normalMap A.det (A.adjugate * B) = A.adjugate.mulVecLin.comp (blockMap A B) := by
  apply LinearMap.ext
  intro y
  change (fun i => A.det * y.1 i + ((A.adjugate * B) *ᵥ y.2) i) =
    A.adjugate *ᵥ (A *ᵥ y.1 + B *ᵥ y.2)
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
  rfl

variable [IsDomain R]

/-- The selected nonzero minor proves equivalence of the actual kernel equations. -/
theorem blockMap_kernel_eq (A : Matrix (Fin r) (Fin r) R[X])
    (B : Matrix (Fin r) (Fin n) R[X]) (hA : A.det ≠ 0) :
    LinearMap.ker (blockMap A B) = LinearMap.ker (normalMap A.det (A.adjugate * B)) := by
  rw [normalMap_eq_adjugate]
  have hinj : Function.Injective A.adjugate.mulVec :=
    Matrix.mulVec_injective_of_det_ne_zero (by rw [Matrix.det_adjugate]; exact pow_ne_zero _ hA)
  ext y
  change blockMap A B y = 0 ↔ A.adjugate *ᵥ blockMap A B y = 0
  constructor
  · intro h
    rw [h, Matrix.mulVec_zero]
  · intro h
    apply hinj
    simpa only [Matrix.mulVec_zero] using h

/-- The full normal-form kernel generation statement with its degree
hypotheses derived from the original block entries. -/
theorem blockMap_kernel_generated (A : Matrix (Fin r) (Fin r) R[X])
    (B : Matrix (Fin r) (Fin n) R[X]) (d : ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ d)
    (hB : ∀ i j, (B i j).natDegree ≤ d)
    (hdet : A.det.Monic) (hdet1 : A.det ≠ 1) :
    LinearMap.ker (blockMap A B) =
      Submodule.span R[X] (Set.range (elementarySolution A.det (A.adjugate * B)) ∪
        smallKernel A.det (A.adjugate * B) (r * d)) := by
  rw [blockMap_kernel_eq A B hdet.ne_zero]
  exact normal_kernel_eq_span A.det hdet hdet1 _ (r * d)
    (determinant_natDegree_le A d hA) (adjugate_mul_natDegree_le A B d hA hB)

end
end Decoupling.HighDim.Hermann
