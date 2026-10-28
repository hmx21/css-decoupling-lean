import Decoupling.HighDim.SparseCircuit

/-! # Actual dense nonzero coefficients equal genuine Laurent support counts -/
namespace Decoupling.HighDim.SparseCircuit
open Circuit LaurentArithmetic DenseShearCompile Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] [DecidableEq K] {D m n h : ℕ} {ι κ : Type*}

def sumSupportCount (word : List (SUM K D ι)) : ℕ :=
  (word.filter fun g => decide (g.weight ≠ 0)).length

theorem sumSupportCount_sum (word : List (SUM K D ι)) :
    sumSupportCount word = (word.map fun g => if g.weight = 0 then 0 else 1).sum := by
  induction word with
  | nil => rfl
  | cons g word ih =>
    by_cases hz : g.weight = 0 <;> simp [sumSupportCount,hz] at ih ⊢ <;> omega

@[simp] theorem sumSupportCount_append (a b : List (SUM K D ι)) :
    sumSupportCount (a ++ b) = sumSupportCount a + sumSupportCount b := by
  simp [sumSupportCount,List.filter_append]

@[simp] theorem sumSupportCount_dual (word : List (SUM K D ι)) :
    sumSupportCount (word.map SUM.dual) = sumSupportCount word := by
  simp [sumSupportCount_sum,List.map_map,SUM.dual,Function.comp_def]

@[simp] theorem sumSupportCount_relabel (e : ι ≃ κ) (word : List (SUM K D ι)) :
    sumSupportCount (word.map fun g => g.relabel e) = sumSupportCount word := by
  simp [sumSupportCount_sum,List.map_map,SUM.relabel,Function.comp_def]

theorem dense_support (v : Dense K D h) :
    (denote v).coeff.support =
      (Finset.univ.filter fun k : Fin (boxSize D h) => v[k] ≠ 0).image (exponentAt D h) := by
  classical
  ext a
  constructor
  · intro ha
    have hb := denote_supported v ha
    refine Finset.mem_image.mpr ⟨exponentIndex a hb,?_,exponentAt_index a hb⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have hn := Finsupp.mem_support_iff.mp ha
    rw [denote_coeff,lookup,dite_eq_left hb] at hn
    exact hn
  · intro ha
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp ha
    rw [Finsupp.mem_support_iff,denote_coeff,lookup_at]
    exact (Finset.mem_filter.mp hk).2

theorem dense_support_card (v : Dense K D h) :
    (denote v).coeff.support.card = ∑ k : Fin (boxSize D h), if v[k] = 0 then 0 else 1 := by
  classical
  rw [dense_support,Finset.card_image_of_injective _ (exponentAt_injective D h),Finset.card_filter]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : v[k] = 0 <;> simp [hk]

theorem upper_support (A : DenseMatrix K D m n h) :
    sumSupportCount (upperWord A) = supportSize (matrixDenote A) := by
  rw [sumSupportCount_sum]
  unfold upperWord
  rw [List.map_ofFn,List.sum_ofFn]
  rw [← (index (D := D) (m := m) (n := n) (h := h)).symm.sum_comp]
  simp only [Function.comp_apply,gateAt,Equiv.apply_symm_apply,Fintype.sum_prod_type]
  unfold supportSize matrixDenote
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  exact (dense_support_card A[i][j]).symm

theorem lower_support (A : DenseMatrix K D n m h) :
    sumSupportCount (lowerWord A) = supportSize (matrixDenote A) := by
  change sumSupportCount ((upperWord A).map fun g => g.relabel (Equiv.sumComm _ _)) = _
  rw [sumSupportCount_relabel,upper_support]

theorem erase_map_sum_length (word : List (SUM K D ι)) :
    (eraseZeroSUM (word.map Layer.sum)).length = sumSupportCount word := by
  induction word with
  | nil => rfl
  | cons g word ih =>
    by_cases hz : g.weight = 0 <;>
      simp [eraseZeroSUM,keep,sumSupportCount,hz] at ih ⊢ <;> omega

theorem erase_map_swap (word : List (SWAP ι)) :
    eraseZeroSUM (word.map (Layer.swap (K := K) (D := D))) = word.map Layer.swap := by
  induction word with
  | nil => rfl
  | cons g word ih => simp_all [eraseZeroSUM,keep]

theorem erase_relabel (e : ι ≃ κ) (word : List (Layer K D ι)) :
    eraseZeroSUM (word.map (DenseCircuitPermutation.relabelLayer e)) =
      (eraseZeroSUM word).map (DenseCircuitPermutation.relabelLayer e) := by
  induction word with
  | nil => rfl
  | cons g word ih =>
    simp only [eraseZeroSUM] at ih
    cases g with
    | sum g =>
      by_cases hz : g.weight = 0 <;>
        simp [eraseZeroSUM,keep,DenseCircuitPermutation.relabelLayer,SUM.relabel,hz,ih]
    | swap g => simp [eraseZeroSUM,keep,DenseCircuitPermutation.relabelLayer,ih]

variable {a b : ℕ}

theorem theta_shear_length (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    (eraseZeroSUM (DenseShearCompile.thetaProgram f g).value).length =
      supportSize (matrixDenote f) + supportSize (matrixDenote g) := by
  simp only [DenseShearCompile.thetaProgram,ArithmeticCost.Work.bind_value,
    ArithmeticCost.Work.pure_value,erase_map_sum_length,twoShearProgram,
    dualWordProgram_value,sumSupportCount_dual,sumSupportCount_append,
    upper_support,lower_support,matrixNegProgram_correct,supportSize_neg]

theorem canonicalTheta_sparse_length (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    (eraseZeroSUM (DenseCircuitPermutation.canonicalThetaProgram f g).value).length ≤
      supportSize (matrixDenote f) + supportSize (matrixDenote g) + n+m := by
  rw [DenseCircuitPermutation.canonicalThetaProgram,ArithmeticCost.Work.bind_value,
    ArithmeticCost.Work.pure_value,erase_relabel,List.length_map]
  simp only [DenseCircuitPermutation.thetaProgramWith,ArithmeticCost.Work.bind_value,
    ArithmeticCost.Work.pure_value,erase_append,List.length_append,erase_map_swap,
    List.length_map,theta_shear_length]
  have hs := DenseCircuitPermutation.compileSum_length n m
    ((DenseCircuitPermutation.canonicalIdentification m n).symm.trans (Equiv.sumComm _ _))
  omega

end Decoupling.HighDim.SparseCircuit
