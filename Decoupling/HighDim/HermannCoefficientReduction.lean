import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Removing one variable by actual coefficient comparison

The coefficient matrix is explicit: its entries are coefficients of the
original polynomial matrix. A solution of last-variable degree below b is
equivalent to a solution of the displayed finite system over the coefficient
ring, with m*(d+b) equations and n*b unknowns. The degree cutoff is an
explicit input of this reduction, to be supplied by HermannMinor.
-/

namespace Decoupling.HighDim.Hermann
open Polynomial Matrix
noncomputable section
variable {R : Type*} [CommRing R] {m n : ℕ}

/-- The finite coefficient matrix over the smaller coefficient ring. -/
def lastCoefficientMatrix (A : Matrix (Fin m) (Fin n) R[X]) (d b : ℕ) :
    Matrix (Fin m × Fin (d + b)) (Fin n × Fin b) R :=
  fun i j => if j.2.val ≤ i.2.val then (A i.1 j.1).coeff (i.2.val - j.2.val) else 0

/-- Reassemble the actual polynomials with the given coefficients. -/
def lastEncode (b : ℕ) (z : (Fin n × Fin b) → R) : Fin n → R[X] :=
  fun j => ((Polynomial.degreeLTEquiv R b).symm (fun k => z (j, k))).val

def lastDecode (b : ℕ) (y : Fin n → R[X]) : (Fin n × Fin b) → R :=
  fun j => (y j.1).coeff j.2.val

theorem lastEncode_degree (b : ℕ) (z : (Fin n × Fin b) → R) (j : Fin n) :
    (lastEncode b z j).degree < (b : WithBot ℕ) :=
  Polynomial.mem_degreeLT.mp ((Polynomial.degreeLTEquiv R b).symm (fun k => z (j, k))).property

theorem lastEncode_decode (b : ℕ) (y : Fin n → R[X])
    (hy : ∀ j, (y j).degree < (b : WithBot ℕ)) : lastEncode b (lastDecode b y) = y := by
  funext j
  exact congrArg Subtype.val ((Polynomial.degreeLTEquiv R b).symm_apply_apply
    ⟨y j, Polynomial.mem_degreeLT.mpr (hy j)⟩)

@[simp] theorem lastDecode_encode (b : ℕ) (z : (Fin n × Fin b) → R) :
    lastDecode b (lastEncode b z) = z := by
  funext j
  exact congrFun ((Polynomial.degreeLTEquiv R b).apply_symm_apply (fun k => z (j.1, k))) j.2

/-- The coefficient formula with its lower-triangular support condition. -/
theorem coeff_mul_monomial_cutoff (P : R[X]) (k l : ℕ) (a : R) :
    (P * Polynomial.monomial l a).coeff k =
      (if l ≤ k then P.coeff (k - l) else 0) * a := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc, Polynomial.coeff_mul_X_pow']
  simp only [Polynomial.coeff_mul_C]
  split <;> simp_all

theorem lastCoefficientMatrix_mulVec (A : Matrix (Fin m) (Fin n) R[X]) (d b : ℕ)
    (z : (Fin n × Fin b) → R) :
    lastCoefficientMatrix A d b *ᵥ z = lastDecode (d + b) (A *ᵥ lastEncode b z) := by
  funext i
  change (∑ j : Fin n × Fin b, lastCoefficientMatrix A d b i j * z j) =
    (∑ j : Fin n, A i.1 j * lastEncode b z j).coeff i.2.val
  rw [Fintype.sum_prod_type, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro j _
  change (∑ k : Fin b, _ * _) =
    (A i.1 j * ∑ k : Fin b, Polynomial.monomial k.val (z (j, k))).coeff i.2.val
  rw [Finset.mul_sum, Polynomial.finsetSum_coeff]
  apply Finset.sum_congr rfl
  intro k _
  exact (coeff_mul_monomial_cutoff (A i.1 j) i.2.val k.val (z (j, k))).symm

/-- Polynomial multiplication respects the strict cutoff, including b=0. -/
theorem product_degree_lt {P Q : R[X]} {d b : ℕ}
    (hP : P.natDegree ≤ d) (hQ : Q.degree < (b : WithBot ℕ)) :
    (P * Q).degree < ((d + b : ℕ) : WithBot ℕ) := by
  have hle : P.degree ≤ (d : WithBot ℕ) :=
    Polynomial.degree_le_natDegree.trans (WithBot.coe_le_coe.mpr hP)
  apply (Polynomial.degree_mul_le _ _).trans_lt
  apply (add_le_add hle (le_refl Q.degree)).trans_lt
  simpa only [Nat.cast_add] using
    (WithBot.add_lt_add_iff_left (by simp : (d : WithBot ℕ) ≠ ⊥)).mpr hQ

/-- Every product row has the exact finite output cutoff. -/
theorem mulVec_degree_lt (A : Matrix (Fin m) (Fin n) R[X]) (d b : ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ d) (y : Fin n → R[X])
    (hy : ∀ j, (y j).degree < (b : WithBot ℕ)) (i : Fin m) :
    ((A *ᵥ y) i).degree < ((d + b : ℕ) : WithBot ℕ) := by
  change (∑ j, A i j * y j).degree < _
  apply (Polynomial.degree_sum_le _ _).trans_lt
  apply (Finset.sup_lt_iff (WithBot.bot_lt_coe _)).mpr
  intro j _
  exact product_degree_lt (hA i j) (hy j)

/-- Last-variable coefficient comparison is equivalent to the actual equation. -/
theorem last_bounded_solution_iff (A : Matrix (Fin m) (Fin n) R[X]) (d b : ℕ)
    (hA : ∀ i j, (A i j).natDegree ≤ d)
    (v : Fin m → R[X]) (hv : ∀ i, (v i).degree < ((d + b : ℕ) : WithBot ℕ)) :
    (∃ y : Fin n → R[X], A *ᵥ y = v ∧ ∀ j, (y j).degree < (b : WithBot ℕ)) ↔
    ∃ z : (Fin n × Fin b) → R, lastCoefficientMatrix A d b *ᵥ z = lastDecode (d + b) v := by
  constructor
  · rintro ⟨y, he, hy⟩
    refine ⟨lastDecode b y, ?_⟩
    rw [lastCoefficientMatrix_mulVec, lastEncode_decode b y hy, he]
  · rintro ⟨z, hz⟩
    refine ⟨lastEncode b z, ?_, lastEncode_degree b z⟩
    rw [lastCoefficientMatrix_mulVec] at hz
    have he := congrArg (lastEncode (d + b)) hz
    rw [lastEncode_decode _ _ (mulVec_degree_lt A d b hA _ (lastEncode_degree b z)),
      lastEncode_decode _ _ hv] at he
    exact he

end
end Decoupling.HighDim.Hermann
