import Decoupling.HighDim.StableFreeResourceCochain
import Decoupling.HighDim.StableFreeEffectiveCochainOutput

/-!
# Explicit polynomial bound for the entire native C4 program

For fixed spatial dimension and fixed actual resolution length, the native
program's field-operation trace and returned coefficient box are bounded by
specified natural-coefficient polynomials in the actual rank/radius budget.
The conversion from this budget to the paper's dense input size is separate.
-/
namespace Decoupling.HighDim.StableFree.Resource
open Polynomial Effective Effective.CochainProgram LaurentArithmetic

def initialEnvelope (D S : ℕ) := completeInitialCost D S S S S S

noncomputable def initialPolynomial (D : ℕ) : Polynomial ℕ :=
  let s : Polynomial ℕ := X
  let h₂ := s+s
  let h₃ := s+h₂
  let h₄ := s+h₃
  let h₅ := s+h₄
  let box := fun z : Polynomial ℕ => (2*z+1)^D
  let factor := 2*box s+1
  (s*s*s*box h₂*factor + s*s*box h₂ +
   s*(s+s)*s*box h₃*factor + s*(s+s)*box h₃ +
   s*(s+s)*s*box h₄*factor + s*(s+s)*box h₄ +
   s*(s+s)*s*box h₄*factor + s*(s+s)*box h₄ +
   s*(s+s)*s*box h₅*factor) +
  (s*(s+s)*s*box h₂*factor + s*(s+s)*box h₂ +
   s*(s+s)*s*box h₂*factor + s*(s+s)*box h₂ +
   s*(s+s)*s*box h₃*factor)

theorem initialPolynomial_eval (D S : ℕ) : (initialPolynomial D).eval S = initialEnvelope D S := by
  simp [initialPolynomial,initialEnvelope,completeInitialCost,Initial.initialCost,
    Initial.radius5,Initial.radius4,Initial.radius3,Initial.radius2,boxSize]

theorem completeInitialCost_le {D c n p e h S : ℕ}
    (hc : c ≤ S) (hn : n ≤ S) (hp : p ≤ S) (he : e ≤ S) (hh : h ≤ S) :
    completeInitialCost D c n p e h ≤ initialEnvelope D S := by
  unfold initialEnvelope completeInitialCost
  apply Nat.add_le_add (Initial.initialCost_mono hc hn hp he hh)
  unfold boxSize Initial.radius3 Initial.radius2
  gcongr

noncomputable def absorbPolynomial (D : ℕ) : Polynomial ℕ :=
  3*((3*X)*(3*X)*(3*X)*(2*(3*X)+1)^D*(2*(2*X+1)^D+1))

theorem absorbPolynomial_eval (D S : ℕ) : (absorbPolynomial D).eval S = absorbEnvelope D S := by
  simp [absorbPolynomial,absorbEnvelope,boxSize]

/-- The initial quotient stage counts as one of the true Schanuel stages. -/
noncomputable def nativeIteratePolynomial (D length : ℕ) : Polynomial ℕ :=
  (iteratedPolynomial D (length+1)).comp (5*X)

theorem nativeIteratePolynomial_eval (D length S : ℕ) :
    (nativeIteratePolynomial D length).eval S = iteratedBound D (length+1) (5*S) := by
  rw [nativeIteratePolynomial,Polynomial.eval_comp,Polynomial.eval_mul,
    Polynomial.eval_ofNat,Polynomial.eval_X,iteratedPolynomial_eval]

noncomputable def nativeBoxPolynomial (D length : ℕ) : Polynomial ℕ :=
  3*nativeIteratePolynomial D length

noncomputable def nativeCostPolynomial (D length : ℕ) : Polynomial ℕ :=
  2*X^2*(2*X+1)^D +
    (initialPolynomial D +
      (C (length+1)*nativeIteratePolynomial D length +
        (absorbPolynomial D).comp (nativeIteratePolynomial D length)))

theorem nativeBoxPolynomial_eval (D length S : ℕ) :
    (nativeBoxPolynomial D length).eval S = 3*iteratedBound D (length+1) (5*S) := by
  rw [nativeBoxPolynomial,Polynomial.eval_mul,Polynomial.eval_ofNat,nativeIteratePolynomial_eval]

theorem nativeCostPolynomial_eval (D length S : ℕ) :
    (nativeCostPolynomial D length).eval S =
      2*S^2*boxSize D S + (initialEnvelope D S +
        ((length+1)*iteratedBound D (length+1) (5*S) + absorbEnvelope D (iteratedBound D (length+1) (5*S)))) := by
  simp only [nativeCostPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_ofNat,Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_C,Polynomial.eval_comp,
    initialPolynomial_eval,nativeIteratePolynomial_eval,absorbPolynomial_eval]
  rfl

variable {K : Type*} {D h₀ length n c : ℕ}

theorem runBox_polynomial (F : DenseTower K D h₀ length n) (G : DenseTower K D h₀ length c)
    (p e rel h S : ℕ) (hb : nativeBudget F G p e rel h ≤ S) :
    runBox F G p e h ≤ (nativeBoxPolynomial D length).eval S := by
  rw [nativeBoxPolynomial_eval]
  exact (native_bounds F G p e rel h S hb).1

variable [Field K] [DecidableEq K] {h totalC totalT : ℕ}
  {C T : CochainComplex (ModuleCat (Laurent K D)) ℤ}

/-- Actual native C4 trace bound, with no supplied polynomial-cost premise.
The tail length l+1 means the complete algorithm has l+2 Schanuel stages. -/
theorem execute_polynomial (cC : StableFree.Coordinates C) (cT : StableFree.Coordinates T)
    (frameC : AlgorithmTwoFiniteComplex.Coordinates C totalC) (frameT : AlgorithmTwoFiniteComplex.Coordinates T totalT)
    (sC : TermSelectors cC.rank totalC) (sT : TermSelectors cT.rank totalT)
    (hC : FrameRealizes cC frameC sC) (hT : FrameRealizes cT frameT sT)
    (equiv : HomotopyEquiv C T) (arrays : NativeArrays K D totalC totalT h)
    (ha : NativeRealizes frameC frameT equiv arrays) (l S : ℕ)
    [C.IsGE 1] [T.IsGE 1] [C.IsStrictlyGE (-(l:ℤ))] [T.IsStrictlyGE (-(l:ℤ))]
    (hb : nativeBudget (tailTower sT arrays.differentialT (l+1)) (tailTower sC arrays.differentialC (l+1))
      (cC.rank 2) (cT.rank 2) (cT.rank 0) h ≤ S) :
    (execute cC cT frameC frameT sC sT hC hT equiv arrays ha l).cost ≤
      (nativeCostPolynomial D (l+1)).eval S := by
  let F := tailTower sT arrays.differentialT (l+1)
  let G := tailTower sC arrays.differentialC (l+1)
  have hc : cC.rank 1 ≤ S := by dsimp [nativeBudget,DenseTower.rankBudget] at hb; omega
  have hn : cT.rank 1 ≤ S := by dsimp [nativeBudget,DenseTower.rankBudget] at hb; omega
  have hp : cC.rank 2 ≤ S := by dsimp [nativeBudget,DenseTower.rankBudget] at hb; omega
  have he : cT.rank 2 ≤ S := by dsimp [nativeBudget,DenseTower.rankBudget] at hb; omega
  have hh : h ≤ S := by dsimp [nativeBudget] at hb; omega
  have hcoeff : cC.rank 1*cC.rank 2+cT.rank 1*cT.rank 2 ≤ 2*S^2 := by
    have h₁ := Nat.mul_le_mul hc hp
    have h₂ := Nat.mul_le_mul hn he
    nlinarith
  have hneg := Nat.mul_le_mul hcoeff (boxSize_mono (D := D) hh)
  have hinit := completeInitialCost_le (D := D) hc hn hp he hh
  have hremain := (native_bounds F G (cC.rank 2) (cT.rank 2) (cT.rank 0) h S hb).2
  rw [nativeCostPolynomial_eval]
  exact (execute_cost cC cT frameC frameT sC sT hC hT equiv arrays ha l).trans
    (Nat.add_le_add hneg (Nat.add_le_add hinit hremain))


/-- The complete native C4 bound in its own actual input budget, without
any caller-supplied intermediate bound or complexity certificate. -/
theorem execute_input_polynomial (cC : StableFree.Coordinates C) (cT : StableFree.Coordinates T)
    (frameC : AlgorithmTwoFiniteComplex.Coordinates C totalC) (frameT : AlgorithmTwoFiniteComplex.Coordinates T totalT)
    (sC : TermSelectors cC.rank totalC) (sT : TermSelectors cT.rank totalT)
    (hC : FrameRealizes cC frameC sC) (hT : FrameRealizes cT frameT sT)
    (equiv : HomotopyEquiv C T) (arrays : NativeArrays K D totalC totalT h)
    (ha : NativeRealizes frameC frameT equiv arrays) (l : ℕ)
    [C.IsGE 1] [T.IsGE 1] [C.IsStrictlyGE (-(l:ℤ))] [T.IsStrictlyGE (-(l:ℤ))] :
    (execute cC cT frameC frameT sC sT hC hT equiv arrays ha l).cost ≤
      (nativeCostPolynomial D (l+1)).eval
        (nativeBudget (tailTower sT arrays.differentialT (l+1))
          (tailTower sC arrays.differentialC (l+1)) (cC.rank 2) (cT.rank 2) (cT.rank 0) h) :=
  execute_polynomial cC cT frameC frameT sC sT hC hT equiv arrays ha l _ (Nat.le_refl _)

end Decoupling.HighDim.StableFree.Resource
