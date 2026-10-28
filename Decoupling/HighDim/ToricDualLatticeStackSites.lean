import Decoupling.HighDim.ToricDualLatticeStack

/-! # Copy-preserving physical sites of a complementary toric stack -/

namespace Decoupling.HighDim.Toric

open Matrix Koszul

noncomputable section
variable (D : ℕ) {ι : Type} (forms complements : ι → ℕ)
  (h : ∀ i, forms i + complements i + 2 = D)

def stackDualSiteEquiv :
    (Σ i, Cell D (forms i + 1) × Translation D) ≃
      (Σ i, Cell D (complements i + 1) × Translation D) :=
  Equiv.sigmaCongrRight (fun i => dualSiteEquiv (by have := h i; omega : (forms i + 1) + (complements i + 1) = D))

@[simp] theorem stackDualSiteEquiv_copy
    (x : Σ i, Cell D (forms i + 1) × Translation D) :
    (stackDualSiteEquiv D forms complements h x).1 = x.1 := rfl

theorem stackDualSiteEquiv_translation (i : ι) (I : Cell D (forms i + 1))
    (n a : Translation D) :
    stackDualSiteEquiv D forms complements h ⟨i, I, n + a⟩ =
      ⟨i, (dualSiteEquiv (by have := h i; omega : (forms i + 1) + (complements i + 1) = D) (I, n)).1,
        (dualSiteEquiv (by have := h i; omega : (forms i + 1) + (complements i + 1) = D) (I, n)).2 + a⟩ := by
  exact congrArg (Sigma.mk i) (dualSiteEquiv_translation _ I n a)

theorem stackDualSiteEquiv_range (i : ι) (I : Cell D (forms i + 1))
    (n : Translation D) (x : Fin D) :
    (((stackDualSiteEquiv D forms complements h ⟨i, I, n⟩).2.2 - n) x).natAbs ≤ 1 :=
  dualSiteEquiv_range _ I n x

variable (K : Type) [Field K] [Fintype ι]

/-- The actual block matrix acts on each actual site exactly as the
copy-preserving dual-cell bijection, with its already computed sign. -/
theorem stackDualMatrix_site (i : ι) (I : Cell D (forms i + 1)) (n : Translation D) :
    stackDualMatrix K D forms complements h *ᵥ
      Pi.single ((Fintype.equivFin (Σ i, Fin (cellCount D (forms i + 1))))
        ⟨i, (Fintype.equivFin _) I⟩) (monomial K n) =
      Pi.single ((Fintype.equivFin (Σ i, Fin (cellCount D (complements i + 1))))
        ⟨i, (Fintype.equivFin _) (dualSiteEquiv (by have := h i; omega : (forms i + 1) + (complements i + 1) = D) (I, n)).1⟩)
        ((-1 : Laurent K D) ^ ((∑ x ∈ Hodge.directions I, x.val) + (forms i + 1)) *
          monomial K (dualSiteEquiv (by have := h i; omega : (forms i + 1) + (complements i + 1) = D) (I, n)).2) := by
  classical
  funext s
  obtain ⟨⟨j, b⟩, rfl⟩ := (Fintype.equivFin (Σ i, Fin (cellCount D (complements i + 1)))).surjective s
  rw [Matrix.mulVec_single]
  simp only [Pi.smul_apply, op_smul_eq_mul, Matrix.col_apply]
  simp only [stackDualMatrix, stackDualCellMatrix, stackMatrix, Matrix.submatrix_apply,
    Equiv.symm_apply_apply]
  by_cases hji : j = i
  · subst j
    rw [Matrix.blockDiagonal'_apply_eq]
    have he := congrFun (dualLatticeMatrix_site K (by have := h i; omega : (forms i + 1) + (complements i + 1) = D) I n) b
    rw [Matrix.mulVec_single] at he
    simp only [Pi.smul_apply, op_smul_eq_mul, Matrix.col_apply] at he
    simpa only [Pi.single_apply, Equiv.apply_eq_iff_eq, Sigma.mk.inj_iff, heq_eq_eq, true_and] using he
  · rw [Matrix.blockDiagonal'_apply_ne _ _ _ hji, zero_mul]
    have hn : (Fintype.equivFin (Σ i, Fin (cellCount D (complements i + 1)))) ⟨j, b⟩ ≠
        (Fintype.equivFin _) ⟨i, (Fintype.equivFin _)
          (dualSiteEquiv (by have := h i; omega : (forms i + 1) + (complements i + 1) = D) (I, n)).1⟩ := by
      intro he
      exact hji (congrArg Sigma.fst ((Fintype.equivFin _).injective he))
    simp [hn]

end
end Decoupling.HighDim.Toric
