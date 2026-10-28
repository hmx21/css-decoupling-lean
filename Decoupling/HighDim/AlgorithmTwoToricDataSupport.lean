import Decoupling.HighDim.AlgorithmTwoToricData
import Decoupling.HighDim.AlgorithmTwoComputedLayersCoordinates

/-!
# Nonpositive exactness of the actual computed toric target

The true stack augmentation is a quasi-isomorphism to the true
single-layer sum, whose terms in nonpositive degrees are zero.
Thus the C4 exactness premise follows from the target construction.
-/
namespace Decoupling.HighDim.AlgorithmTwoToricData
open CategoryTheory HomologicalComplex
open AlgorithmTwoComparison
noncomputable section
variable (D : ℕ) (t : Vector ℕ (D - 1)) (K : Type) [Field K]

theorem nativeStack_isGE_one : (nativeStack D t K).IsGE 1 := by
  rw [CochainComplex.isGE_iff]
  intro n hn
  rw [exactAt_iff_of_quasiIsoAt (stackAugmentation K D (Toric.copyForms D (multiplicities D t))) n]
  apply ExactAt.of_isZero
  apply AlgorithmTwoComputedLayers.stackZeroModel_outside
  rintro ⟨j, hj⟩
  have : 0 ≤ (j.val : ℤ) := Int.natCast_nonneg _
  omega

theorem nativeStack_nonpositive_exact (n : ℤ) (hn : n ≤ 0) :
    (nativeStack D t K).ExactAt n := by
  let : (nativeStack D t K).IsGE 1 := nativeStack_isGE_one D t K
  exact (nativeStack D t K).exactAt_of_isGE 1 n (by omega)

end
end Decoupling.HighDim.AlgorithmTwoToricData
