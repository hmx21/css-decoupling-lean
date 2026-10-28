import Decoupling.HighDim.StableFreeEffectiveInitialCorrectness
import Decoupling.HighDim.LaurentArithmeticBounds

/-! # HD012 exact arithmetic count of the initial Schanuel matrix construction -/
namespace Decoupling.HighDim.StableFree.Effective.Initial
open ArithmeticCost LaurentArithmetic
variable {K : Type*} [Field K] {D c n p e rel h : ℕ}

def initialCost (D c n p e h : ℕ) : ℕ :=
  n*p*c*boxSize D (radius2 h)*(2*boxSize D h+1) + n*p*boxSize D (radius2 h) +
  c*(e+p)*n*boxSize D (radius3 h)*(2*boxSize D h+1) + c*(e+p)*boxSize D (radius3 h) +
  n*(e+p)*c*boxSize D (radius4 h)*(2*boxSize D h+1) + n*(e+p)*boxSize D (radius4 h) +
  p*(e+p)*c*boxSize D (radius4 h)*(2*boxSize D h+1) + p*(e+p)*boxSize D (radius4 h) +
  e*(e+p)*n*boxSize D (radius5 h)*(2*boxSize D h+1)

namespace Inputs
variable (i : Inputs K D c n p e rel h)

@[simp] theorem makeL_cost :
    i.makeL.cost = n*p*c*boxSize D (radius2 h)*(2*boxSize D h+1) +
      n*p*boxSize D (radius2 h) := by
  simp [makeL, Work.bind_cost]

@[simp] theorem makeR_cost (L : DenseMatrix K D n (e+p) (radius2 h)) :
    (i.makeR L).cost = c*(e+p)*n*boxSize D (radius3 h)*(2*boxSize D h+1) +
      c*(e+p)*boxSize D (radius3 h) := by
  simp [makeR, Work.bind_cost]

@[simp] theorem makeQN_cost (L : DenseMatrix K D n (e+p) (radius2 h))
    (R : DenseMatrix K D c (e+p) (radius3 h)) :
    (i.makeQN L R).cost = n*(e+p)*c*boxSize D (radius4 h)*(2*boxSize D h+1) +
      n*(e+p)*boxSize D (radius4 h) := by
  simp [makeQN, Work.bind_cost]

@[simp] theorem makeQP_cost (R : DenseMatrix K D c (e+p) (radius3 h)) :
    (i.makeQP R).cost = p*(e+p)*c*boxSize D (radius4 h)*(2*boxSize D h+1) +
      p*(e+p)*boxSize D (radius4 h) := by
  simp [makeQP, Work.bind_cost]

@[simp] theorem makeQ_cost (QN : DenseMatrix K D n (e+p) (radius4 h))
    (QP : DenseMatrix K D p (e+p) (radius4 h)) :
    (i.makeQ QN QP).cost = e*(e+p)*n*boxSize D (radius5 h)*(2*boxSize D h+1) := by
  simp [makeQ, Work.bind_cost]

/-- The full recorded trace has this exact input-size-dependent length. -/
theorem run_cost : i.run.cost = initialCost D c n p e h := by
  simp only [run, Work.bind_cost, makeL_cost, makeR_cost, makeQN_cost, makeQP_cost,
    makeQ_cost, Work.pure_cost]
  unfold initialCost
  omega

end Inputs

theorem radius5_eq (h : ℕ) : radius5 h = 5*h := by
  unfold radius5 radius4 radius3 radius2
  omega

theorem initialCost_mono {c' n' p' e' h' : ℕ}
    (hc : c ≤ c') (hn : n ≤ n') (hp : p ≤ p') (he : e ≤ e') (hh : h ≤ h') :
    initialCost D c n p e h ≤ initialCost D c' n' p' e' h' := by
  have h₂ : boxSize D (radius2 h) ≤ boxSize D (radius2 h') :=
    boxSize_mono (by dsimp [radius2]; omega)
  have h₃ : boxSize D (radius3 h) ≤ boxSize D (radius3 h') :=
    boxSize_mono (by dsimp [radius3,radius2]; omega)
  have h₄ : boxSize D (radius4 h) ≤ boxSize D (radius4 h') :=
    boxSize_mono (by dsimp [radius4,radius3,radius2]; omega)
  have h₅ : boxSize D (radius5 h) ≤ boxSize D (radius5 h') :=
    boxSize_mono (by dsimp [radius5,radius4,radius3,radius2]; omega)
  have h₁ : boxSize D h ≤ boxSize D h' := boxSize_mono hh
  unfold initialCost
  gcongr

end Decoupling.HighDim.StableFree.Effective.Initial
