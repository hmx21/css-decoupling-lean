import Decoupling.HighDim.AlgorithmInputSizeGlobal
import Decoupling.HighDim.AlgorithmTwoPipelineInput

/-!
# HD012 original pipeline input and the manuscript's exact dense size

The size is the number of coefficient slots in the original adjacent
differentials. The total-basis square matrix used internally is not used
as a replacement size measure. Its rank and the radius are bounded from
the actual split-profile input whenever the total rank is nonzero.
-/
namespace Decoupling.HighDim.AlgorithmInputSize
open CategoryTheory
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

theorem sum_fin_interval (r : ℤ → ℕ) (L : ℕ) :
    (∑ i : Fin (2*L+1), r (-(L : ℤ)+(i : ℤ))) = rankSum r L := by
  unfold rankSum
  apply Finset.sum_bij (fun (i : Fin (2*L+1)) _ => -(L : ℤ)+(i : ℤ))
  · intro i _
    simp only [Finset.mem_Icc]
    have := i.isLt
    omega
  · intro i _ j _ he
    apply Fin.ext
    omega
  · intro j hj
    have hj' := Finset.mem_Icc.mp hj
    refine ⟨⟨(j+L).toNat, by omega⟩, Finset.mem_univ _, ?_⟩
    change -(L : ℤ)+((j+L).toNat : ℤ)=j
    omega
  · intro i _
    rfl

variable {K : Type} [Field K] {D L h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L : ℤ))] [C.IsStrictlyLE (L : ℤ)]

omit [C.IsStrictlyGE (-(L : ℤ))] [C.IsStrictlyLE (L : ℤ)] in
theorem pipeline_inputRank_eq :
    AlgorithmTwoPipeline.inputRank coords L = rankSum coords.rank L :=
  sum_fin_interval coords.rank L

theorem pipeline_rank_le (j : ℤ) :
    coords.rank j ≤ AlgorithmTwoPipeline.inputRank coords L := by
  by_cases hj : j ∈ Finset.Icc (-(L : ℤ)) L
  · rw [pipeline_inputRank_eq]
    exact Finset.single_le_sum (f := coords.rank) (fun _ _ => Nat.zero_le _) hj
  · have hz : coords.rank j = 0 := AlgorithmTwoPipeline.outside_zero (L := L) coords j (by
      simp only [Finset.mem_Icc] at hj
      dsimp [AlgorithmTwoPipeline.inputLength]
      omega)
    rw [hz]
    exact Nat.zero_le _

/-- This literal quantity counts exactly all coefficients of each original
adjacent differential in the common exponent box, including zero coefficients. -/
def paperCoefficientCount : ℕ := denseSize coords.rank D L h

theorem pipeline_homology_augmentation
    (inp : AlgorithmTwoPipeline.Input (D := D) (L := L) (h := h) coords) (j : ℤ) :
    TrivialLayers.AugmentationAction (C.homology j) := by
  obtain ⟨old,⟨e⟩⟩ := inp.formal
  exact AlgorithmTwoComputedLayers.nativeHomology_augmentation K D old e j

/-- The original profile proves all size premises; no rank or radius
certificate is an extra assumption about the code. -/
theorem pipeline_dense_budget
    (inp : AlgorithmTwoPipeline.Input (D := D) (L := L) (h := h) coords)
    (hD : 0 < D) (hnonzero : 0 < AlgorithmTwoPipeline.inputRank coords L) :
    AlgorithmTwoPipeline.inputRank coords L+h ≤
      (2*(2*L+1)+1)*paperCoefficientCount (D := D) (L := L) (h := h) coords := by
  rw [pipeline_inputRank_eq] at hnonzero ⊢
  exact native_dense_budget coords L h hD (pipeline_homology_augmentation coords inp) hnonzero

end
end Decoupling.HighDim.AlgorithmInputSize
