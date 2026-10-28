import Decoupling.HighDim.StableFreeResourceCochainPolynomial

/-!
# Original term ranks control the complete native C4 budget

The tail towers contain actual original differential slices. Their rank
sums are bounded from the original term ranks by induction, rather than
accepted as a separate certificate. All actual stabilized free ranks and
check-row counts obey the same derived linear input budget.
-/
namespace Decoupling.HighDim.StableFree.Resource
open Polynomial Effective Effective.CochainProgram LaurentArithmetic
variable {K : Type*} {D h : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

theorem differentialTower_rankSum_le (rank : ℕ → ℕ)
    (matrices : ∀ i, DenseMatrix K D (rank i) (rank (i+1)) h)
    (length s : ℕ) (hr : ∀ i, rank i ≤ s) :
    (DenseTower.ofDifferentials rank matrices length).rankSum ≤ length*s := by
  induction length generalizing rank with
  | zero => simp [DenseTower.ofDifferentials,DenseTower.rankSum]
  | succ length ih =>
      have hi := ih (fun i => rank (i+1)) (fun i => matrices (i+1)) (fun i => hr (i+1))
      change rank 1 + (DenseTower.ofDifferentials (fun i => rank (i+1)) (fun i => matrices (i+1)) length).rankSum ≤ _
      nlinarith [hr 1]

theorem tailTower_rankSum_le {rank : ℤ → ℕ} {total : ℕ}
    (selectors : TermSelectors rank total) (A : DenseMatrix K D total total h)
    (length s : ℕ) (hr : ∀ j, rank j ≤ s) :
    (tailTower selectors A length).rankSum ≤ length*s :=
  differentialTower_rankSum_le (fun i => rank (1-(i:ℤ))) (tailArrays selectors A)
    length s (fun i => hr (1-(i:ℤ)))

theorem stabilized_ranks_le_budget {h₀ length n c : ℕ}
    (F : DenseTower K D h₀ length n) (G : DenseTower K D h₀ length c) (p e rel h : ℕ) :
    p+(n+(F.ranks G).2) ≤ nativeBudget F G p e rel h ∧
    p+(c+(F.ranks G).1) ≤ nativeBudget F G p e rel h ∧
    c+(p+(n+(F.ranks G).2)) ≤ nativeBudget F G p e rel h ∧
    n+(p+(c+(F.ranks G).1)) ≤ nativeBudget F G p e rel h := by
  have hr := DenseTower.ranks_sum F G
  dsimp [nativeBudget,DenseTower.rankBudget]
  omega

variable [Field K]

omit [Field K] in
/-- Derived budget, including both actual tail sums, relation rank and
radius. The coefficient 2*l+9 includes the initial two enlarged factors. -/
theorem uniform_native_budget {rC rT : ℤ → ℕ} {totalC totalT : ℕ}
    (sC : TermSelectors rC totalC) (sT : TermSelectors rT totalT)
    (arrays : NativeArrays K D totalC totalT h) (l s : ℕ)
    (hC : ∀ j, rC j ≤ s) (hT : ∀ j, rT j ≤ s) (hh : h ≤ s) :
    nativeBudget (tailTower sT arrays.differentialT (l+1)) (tailTower sC arrays.differentialC (l+1))
      (rC 2) (rT 2) (rT 0) h ≤ (2*l+9)*s := by
  have hF := tailTower_rankSum_le sT arrays.differentialT (l+1) s hT
  have hG := tailTower_rankSum_le sC arrays.differentialC (l+1) s hC
  dsimp [nativeBudget,DenseTower.rankBudget]
  nlinarith [hC 1,hC 2,hT 0,hT 1,hT 2]

noncomputable def budgetPolynomial (l : ℕ) : Polynomial ℕ := C (2*l+9)*X

noncomputable def uniformCostPolynomial (D l : ℕ) : Polynomial ℕ :=
  (nativeCostPolynomial D (l+1)).comp (budgetPolynomial l)

noncomputable def uniformBoxPolynomial (D l : ℕ) : Polynomial ℕ :=
  (nativeBoxPolynomial D (l+1)).comp (budgetPolynomial l)

theorem budgetPolynomial_eval (l s : ℕ) : (budgetPolynomial l).eval s = (2*l+9)*s := by
  rw [budgetPolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X]

theorem uniformCostPolynomial_eval (D l s : ℕ) :
    (uniformCostPolynomial D l).eval s = (nativeCostPolynomial D (l+1)).eval ((2*l+9)*s) := by
  rw [uniformCostPolynomial,Polynomial.eval_comp,budgetPolynomial_eval]

theorem uniformBoxPolynomial_eval (D l s : ℕ) :
    (uniformBoxPolynomial D l).eval s = (nativeBoxPolynomial D (l+1)).eval ((2*l+9)*s) := by
  rw [uniformBoxPolynomial,Polynomial.eval_comp,budgetPolynomial_eval]

omit [Field K] in
/-- All actual stabilization ranks are controlled directly by original
term ranks, with no assumed rank-sum bound. -/
theorem uniform_stabilized_ranks {rC rT : ℤ → ℕ} {totalC totalT : ℕ}
    (sC : TermSelectors rC totalC) (sT : TermSelectors rT totalT)
    (arrays : NativeArrays K D totalC totalT h) (l s : ℕ)
    (hC : ∀ j, rC j ≤ s) (hT : ∀ j, rT j ≤ s) (hh : h ≤ s) :
    let F := tailTower sT arrays.differentialT (l+1)
    let G := tailTower sC arrays.differentialC (l+1)
    let extraC := rC 2+(rT 1+(F.ranks G).2)
    let extraT := rC 2+(rC 1+(F.ranks G).1)
    extraC ≤ (budgetPolynomial l).eval s ∧ extraT ≤ (budgetPolynomial l).eval s ∧
      rC 1+extraC ≤ (budgetPolynomial l).eval s ∧ rT 1+extraT ≤ (budgetPolynomial l).eval s := by
  have hb := uniform_native_budget sC sT arrays l s hC hT hh
  have hr := stabilized_ranks_le_budget (tailTower sT arrays.differentialT (l+1))
    (tailTower sC arrays.differentialC (l+1)) (rC 2) (rT 2) (rT 0) h
  dsimp only
  rw [budgetPolynomial_eval]
  exact ⟨hr.1.trans hb,hr.2.1.trans hb,hr.2.2.1.trans hb,hr.2.2.2.trans hb⟩

omit [Field K] in
theorem uniform_output_box {rC rT : ℤ → ℕ} {totalC totalT : ℕ}
    (sC : TermSelectors rC totalC) (sT : TermSelectors rT totalT)
    (arrays : NativeArrays K D totalC totalT h) (l s : ℕ)
    (hC : ∀ j, rC j ≤ s) (hT : ∀ j, rT j ≤ s) (hh : h ≤ s) :
    runBox (tailTower sT arrays.differentialT (l+1)) (tailTower sC arrays.differentialC (l+1))
      (rC 2) (rT 2) h ≤ (uniformBoxPolynomial D l).eval s := by
  rw [uniformBoxPolynomial_eval]
  exact runBox_polynomial _ _ _ _ _ _ _ (uniform_native_budget sC sT arrays l s hC hT hh)

variable [DecidableEq K] {totalC totalT : ℕ}
  {C T : CochainComplex (ModuleCat (Laurent K D)) ℤ}

/-- Final C4 cost bound from original term ranks and original array radius.
The full algorithm derives these input caps from its actual total frames. -/
theorem execute_uniform_polynomial (cC : StableFree.Coordinates C) (cT : StableFree.Coordinates T)
    (frameC : AlgorithmTwoFiniteComplex.Coordinates C totalC) (frameT : AlgorithmTwoFiniteComplex.Coordinates T totalT)
    (sC : TermSelectors cC.rank totalC) (sT : TermSelectors cT.rank totalT)
    (hC : FrameRealizes cC frameC sC) (hT : FrameRealizes cT frameT sT)
    (equiv : HomotopyEquiv C T) (arrays : NativeArrays K D totalC totalT h)
    (ha : NativeRealizes frameC frameT equiv arrays) (l s : ℕ)
    [C.IsGE 1] [T.IsGE 1] [C.IsStrictlyGE (-(l:ℤ))] [T.IsStrictlyGE (-(l:ℤ))]
    (hrC : ∀ j, cC.rank j ≤ s) (hrT : ∀ j, cT.rank j ≤ s) (hh : h ≤ s) :
    (execute cC cT frameC frameT sC sT hC hT equiv arrays ha l).cost ≤
      (uniformCostPolynomial D l).eval s := by
  rw [uniformCostPolynomial_eval]
  exact execute_polynomial cC cT frameC frameT sC sT hC hT equiv arrays ha l _
    (uniform_native_budget sC sT arrays l s hrC hrT hh)

end Decoupling.HighDim.StableFree.Resource
