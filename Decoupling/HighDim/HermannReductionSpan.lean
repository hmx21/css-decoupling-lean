import Decoupling.HighDim.HermannReduction

/-!
# Generation by elementary solutions and lower-last-degree solutions

This proves the actual kernel-span assertion used by Hermann induction after
monic-minor normalization. It is a reduction lemma, not the final uniform
multivariate degree bound: the small-last-degree solutions still need to be
expanded over the polynomial ring in one fewer variable.
-/

namespace Decoupling.HighDim.Hermann
open Polynomial Matrix
noncomputable section
variable {R : Type*} [CommRing R] {r n : ℕ}

def elementaryMap (δ : R[X]) (C : Matrix (Fin r) (Fin n) R[X]) :
    (Fin n → R[X]) →ₗ[R[X]] ((Fin r → R[X]) × (Fin n → R[X])) where
  toFun := elementaryCombination δ C
  map_add' a b := by
    apply Prod.ext
    · change -(C *ᵥ (a + b)) = -(C *ᵥ a) + -(C *ᵥ b)
      rw [Matrix.mulVec_add, neg_add]
    · funext j
      change δ * (a j + b j) = δ * a j + δ * b j
      exact mul_add _ _ _
  map_smul' a b := by
    apply Prod.ext
    · change -(C *ᵥ (a • b)) = a • -(C *ᵥ b)
      rw [Matrix.mulVec_smul, smul_neg]
    · funext j
      change δ * (a * b j) = a * (δ * b j)
      ring

/-- The finitely many canonical solutions coming from the normal-form minor. -/
def elementarySolution (δ : R[X]) (C : Matrix (Fin r) (Fin n) R[X]) (j : Fin n) :=
  elementaryCombination δ C (Pi.single j 1)

theorem elementaryCombination_eq_sum (δ : R[X]) (C : Matrix (Fin r) (Fin n) R[X])
    (q : Fin n → R[X]) :
    elementaryCombination δ C q = ∑ j, q j • elementarySolution δ C j := by
  have hq : q = ∑ j, q j • Pi.single j 1 := by
    ext k
    simp [Pi.single_apply]
  change elementaryMap δ C q = _
  nth_rw 1 [hq]
  rw [map_sum]
  simp only [map_smul]
  rfl

/-- Actual kernel solutions satisfying the strict last-variable cutoff. -/
def smallKernel (δ : R[X]) (C : Matrix (Fin r) (Fin n) R[X]) (M : ℕ) :
    Set ((Fin r → R[X]) × (Fin n → R[X])) :=
  {y | y ∈ LinearMap.ker (normalMap δ C) ∧
    (∀ i, (y.1 i).degree < (M : WithBot ℕ)) ∧
    ∀ j, (y.2 j).degree < (M : WithBot ℕ)}

variable [IsDomain R]

/-- Hermann's genuine one-variable elimination step for the entire kernel.
The right side is a span in the original polynomial module; exactness of this
span is proved, never supplied as a certificate. -/
theorem normal_kernel_eq_span (δ : R[X]) (hδ : δ.Monic) (hδ1 : δ ≠ 1)
    (C : Matrix (Fin r) (Fin n) R[X]) (M : ℕ) (hδM : δ.natDegree ≤ M)
    (hC : ∀ i j, (C i j).natDegree ≤ M) :
    LinearMap.ker (normalMap δ C) =
      Submodule.span R[X] (Set.range (elementarySolution δ C) ∪ smallKernel δ C M) := by
  apply le_antisymm
  · intro y hy
    rw [reduction_decomposition δ C y]
    apply Submodule.add_mem
    · rw [elementaryCombination_eq_sum]
      apply Submodule.sum_mem
      intro j _
      apply Submodule.smul_mem
      exact Submodule.subset_span (Or.inl ⟨j, rfl⟩)
    · apply Submodule.subset_span
      apply Or.inr
      refine ⟨reduceSolution_mem_ker δ C y hy,
        reduceSolution_head_degree δ hδ hδ1 C M hC y hy, ?_⟩
      intro j
      exact (reduceSolution_tail_degree δ hδ C y j).trans_le
        (Polynomial.degree_le_natDegree.trans (WithBot.coe_le_coe.mpr hδM))
  · apply Submodule.span_le.mpr
    rintro y (⟨j, rfl⟩ | hy)
    · exact elementaryCombination_mem_ker δ C _
    · exact hy.1

end
end Decoupling.HighDim.Hermann
