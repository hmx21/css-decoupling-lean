import Decoupling.HighDim.KoszulFaces
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

/-!
# The signed Koszul chain complex in every dimension

Source: `drafts/main.tex:370–382`, equation `eq:koszul`.
The differential is the stated alternating sum on actual ordered cells.
The proof of its square-zero identity pairs the two ways of deleting two
directions; the signs cancel over every commutative ring.

This file constructs a native `ChainComplex` with finite free terms.
Exactness of the Laurent specialization is a separate assertion and is
not asserted or assumed here.
-/

namespace Decoupling.HighDim.Koszul

open CategoryTheory CategoryTheory.Preadditive

noncomputable section

variable (A : Type*) [CommRing A] {D : ℕ} (w : Fin D → A)

/-- `∂_(k+1) = ∑ i (-1)^i w_(I_i) e_(I\i)` in the actual ordered basis. -/
def boundary (k : ℕ) :
    ModuleCat.of A (Term A D (k + 1)) ⟶ ModuleCat.of A (Term A D k) :=
  ∑ i : Fin (k + 1), (-1 : ℤ) ^ i.val • weightedFace A w k i

/-- The differential on a basis vector is exactly the paper's signed
ordered-subset formula. The first index is zero, hence the paper's
one-based sign `(-1)^(a-1)` is `(-1)^i` here. -/
theorem boundary_basis (k : ℕ) (I : Cell D (k + 1)) :
    boundary A w k (Finsupp.single I 1) =
      ∑ i : Fin (k + 1), Finsupp.single (face I i) ((-1 : A) ^ i.val * w (I i)) := by
  change (boundary A w k).hom (Finsupp.single I 1) = _
  simp [boundary, weightedFace, Finsupp.smul_single, zsmul_eq_mul]

/-- Pair the lower triangle of two deletions with the upper triangle.
This is the weighted version of the standard alternating-face proof. -/
theorem boundary_squared (k : ℕ) : boundary A w (k + 1) ≫ boundary A w k = 0 := by
  classical
  dsimp only [boundary]
  simp only [comp_sum, sum_comp, ← Finset.sum_product']
  let P := Fin (k + 1) × Fin (k + 2)
  let S : Finset P := {ij : P | ij.2.val ≤ ij.1.val}
  rw [Finset.univ_product_univ, ← Finset.sum_add_sum_compl S, ← eq_neg_iff_add_eq_zero,
    ← Finset.sum_neg_distrib]
  let φ : ∀ ij : P, ij ∈ S → P := fun ij hij =>
    (Fin.castLT ij.2 (lt_of_le_of_lt (Finset.mem_filter.mp hij).right ij.1.is_lt), ij.1.succ)
  apply Finset.sum_bij φ
  · intro ij hij
    simp_rw [S, φ, Finset.compl_filter, Finset.mem_filter_univ, Fin.val_succ,
      Fin.val_castLT] at hij ⊢
    omega
  · rintro ⟨i, j⟩ hij ⟨i', j'⟩ hij' h
    rw [Prod.mk_inj]
    exact ⟨by simpa [φ] using! congr_arg Prod.snd h,
      by simpa [φ, Fin.castSucc_castLT] using!
        congr_arg Fin.castSucc (congr_arg Prod.fst h)⟩
  · rintro ⟨i', j'⟩ hij'
    simp_rw [S, Finset.compl_filter, Finset.mem_filter_univ, not_le] at hij'
    refine ⟨(j'.pred ?_, Fin.castSucc i'), ?_, ?_⟩
    · rintro rfl
      simp only [Fin.val_zero, not_lt_zero] at hij'
    · simpa [S] using! Nat.le_sub_one_of_lt hij'
    · simp only [φ, Fin.castLT_castSucc, Fin.succ_pred]
  · rintro ⟨i, j⟩ hij
    dsimp
    simp only [zsmul_comp, comp_zsmul, smul_smul, ← neg_smul]
    congr 1
    · simp only [φ, Fin.val_succ, pow_add, pow_one, mul_neg, neg_neg, mul_one]
      apply mul_comm
    · apply weightedFace_comp
      simpa [S] using! hij

/-- The native, nonnegative-degree Koszul chain complex. -/
def complex : ChainComplex (ModuleCat A) ℕ :=
  ChainComplex.of (fun k => ModuleCat.of A (Term A D k))
    (boundary A w) (boundary_squared A w)

@[simp] theorem complex_X (k : ℕ) : (complex A w).X k = ModuleCat.of A (Term A D k) := rfl

@[simp] theorem complex_d (k : ℕ) : (complex A w).d (k + 1) k = boundary A w k := by
  simp [complex]

instance termFinite (k : ℕ) : Module.Finite A (Term A D k) :=
  Module.Finite.of_basis (Finsupp.basisSingleOne : Module.Basis (Cell D k) A (Term A D k))

/-- Above the ambient dimension there are no coordinate cells. -/
theorem cell_isEmpty {k : ℕ} (h : D < k) : IsEmpty (Cell D k) := by
  refine ⟨fun I => ?_⟩
  have hc := Fintype.card_le_of_injective I I.injective
  simp only [Fintype.card_fin] at hc
  omega

/-- The complex has zero terms above `D`, by the actual absence of basis cells. -/
theorem term_subsingleton {k : ℕ} (h : D < k) : Subsingleton (Term A D k) := by
  let := cell_isEmpty (D := D) h
  infer_instance

/-- The polynomial convention of the manuscript, with `w_i = x_i - 1`. -/
def laurentComplex (K : Type*) [CommRing K] (D : ℕ) :
    ChainComplex (ModuleCat (Laurent K D)) ℕ :=
  complex (Laurent K D) (difference K)

end

end Decoupling.HighDim.Koszul
