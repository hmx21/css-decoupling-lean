import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Domain
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The genuine monic-minor reduction in Hermann's argument

This is the algebraic reduction of the system `(δ I | C) y = 0`.
The minor δ is monic in the last variable. Dividing the free coordinates
by δ writes every solution as elementary solutions plus a solution whose
last-variable degrees are strictly bounded. The general degree theorem
still requires constructing this normal form from an arbitrary matrix,
choosing a degree-preserving change of variables, and induction on variables.
No assertion of the full Hermann bound is made here.
-/

namespace Decoupling.HighDim.Hermann

open Polynomial Matrix
noncomputable section
variable {R : Type*} [CommRing R] {r n : ℕ}

/-- The actual normal-form polynomial system. -/
def normalMap (δ : R[X]) (C : Matrix (Fin r) (Fin n) R[X]) :
    ((Fin r → R[X]) × (Fin n → R[X])) →ₗ[R[X]] (Fin r → R[X]) where
  toFun y i := δ * y.1 i + (C *ᵥ y.2) i
  map_add' y z := by
    funext i
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply, Matrix.mulVec_add, mul_add]
    ring
  map_smul' a y := by
    funext i
    simp only [Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul,
      Matrix.mulVec_smul, RingHom.id_apply]
    ring

/-- The elementary kernel contribution with arbitrary free coefficients. -/
def elementaryCombination (δ : R[X]) (C : Matrix (Fin r) (Fin n) R[X])
    (q : Fin n → R[X]) : (Fin r → R[X]) × (Fin n → R[X]) :=
  (-(C *ᵥ q), fun j => δ * q j)

theorem elementaryCombination_mem_ker (δ : R[X]) (C : Matrix (Fin r) (Fin n) R[X])
    (q : Fin n → R[X]) : elementaryCombination δ C q ∈ LinearMap.ker (normalMap δ C) := by
  funext i
  change δ * (-(C *ᵥ q) i) + (C *ᵥ (fun j => δ * q j)) i = 0
  have he : (C *ᵥ (fun j => δ * q j)) i = δ * (C *ᵥ q) i := by
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  ring

/-- Reduce the free coordinates by genuine polynomial division. -/
def reduceSolution (δ : R[X]) (C : Matrix (Fin r) (Fin n) R[X])
    (y : (Fin r → R[X]) × (Fin n → R[X])) :=
  y - elementaryCombination δ C (fun j => y.2 j /ₘ δ)

@[simp] theorem reduceSolution_tail (δ : R[X]) (C : Matrix (Fin r) (Fin n) R[X])
    (y : (Fin r → R[X]) × (Fin n → R[X])) (j : Fin n) :
    (reduceSolution δ C y).2 j = y.2 j %ₘ δ :=
  (Polynomial.modByMonic_eq_sub_mul_div (y.2 j) δ).symm

theorem reduceSolution_mem_ker (δ : R[X]) (C : Matrix (Fin r) (Fin n) R[X])
    (y : (Fin r → R[X]) × (Fin n → R[X])) (hy : y ∈ LinearMap.ker (normalMap δ C)) :
    reduceSolution δ C y ∈ LinearMap.ker (normalMap δ C) :=
  Submodule.sub_mem _ hy (elementaryCombination_mem_ker δ C _)

/-- Division leaves exactly the elementary contribution plus the remainder solution. -/
theorem reduction_decomposition (δ : R[X]) (C : Matrix (Fin r) (Fin n) R[X])
    (y : (Fin r → R[X]) × (Fin n → R[X])) :
    y = elementaryCombination δ C (fun j => y.2 j /ₘ δ) + reduceSolution δ C y := by
  unfold reduceSolution
  abel

variable [IsDomain R]

/-- Every free remainder has last-variable degree below that of the minor. -/
theorem reduceSolution_tail_degree (δ : R[X]) (hδ : δ.Monic)
    (C : Matrix (Fin r) (Fin n) R[X])
    (y : (Fin r → R[X]) × (Fin n → R[X])) (j : Fin n) :
    ((reduceSolution δ C y).2 j).degree < δ.degree := by
  rw [reduceSolution_tail]
  exact Polynomial.degree_modByMonic_lt _ hδ

/-- The controlled coordinates have the expected strict degree bound.
The statement uses `degree` so that zero coordinates also satisfy the bound M=0. -/
theorem normal_head_degree_lt (δ : R[X]) (hδ : δ.Monic) (hδ1 : δ ≠ 1)
    (C : Matrix (Fin r) (Fin n) R[X]) (M : ℕ)
    (hC : ∀ i j, (C i j).natDegree ≤ M)
    (y : (Fin r → R[X]) × (Fin n → R[X]))
    (hy : y ∈ LinearMap.ker (normalMap δ C))
    (htail : ∀ j, (y.2 j).natDegree < δ.natDegree) (i : Fin r) :
    (y.1 i).degree < (M : WithBot ℕ) := by
  by_cases hi : y.1 i = 0
  · simp [hi]
  have heq : δ * y.1 i = -(C *ᵥ y.2) i := by
    have he := congrFun hy i
    change δ * y.1 i + (C *ᵥ y.2) i = 0 at he
    exact eq_neg_of_add_eq_zero_left he
  have hprod : (δ * y.1 i).natDegree = δ.natDegree + (y.1 i).natDegree :=
    Polynomial.natDegree_mul hδ.ne_zero hi
  have hsum : ((C *ᵥ y.2) i).natDegree ≤ M + (δ.natDegree - 1) := by
    change (∑ j, C i j * y.2 j).natDegree ≤ _
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j _
    exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hC i j)
      (Nat.le_sub_one_of_lt (htail j)))
  have hdeg := congrArg Polynomial.natDegree heq
  rw [hprod, Polynomial.natDegree_neg] at hdeg
  have hpos : 0 < δ.natDegree := hδ.natDegree_pos.mpr hδ1
  apply (Polynomial.natDegree_lt_iff_degree_lt hi).mp
  omega

/-- The actual reduced solution has all controlled coordinates below M. -/
theorem reduceSolution_head_degree (δ : R[X]) (hδ : δ.Monic) (hδ1 : δ ≠ 1)
    (C : Matrix (Fin r) (Fin n) R[X]) (M : ℕ)
    (hC : ∀ i j, (C i j).natDegree ≤ M)
    (y : (Fin r → R[X]) × (Fin n → R[X]))
    (hy : y ∈ LinearMap.ker (normalMap δ C)) (i : Fin r) :
    ((reduceSolution δ C y).1 i).degree < (M : WithBot ℕ) :=
  normal_head_degree_lt δ hδ hδ1 C M hC _ (reduceSolution_mem_ker δ C y hy)
    (fun j => by rw [reduceSolution_tail]; exact Polynomial.natDegree_modByMonic_lt _ hδ hδ1) i

end
end Decoupling.HighDim.Hermann
