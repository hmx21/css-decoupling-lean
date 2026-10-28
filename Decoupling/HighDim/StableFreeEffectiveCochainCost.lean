import Decoupling.HighDim.StableFreeEffectiveCochainNative

/-! Explicit actual trace and output-box bounds for the complete native C4 run. -/
namespace Decoupling.HighDim.StableFree.Effective.CochainProgram
open Matrix LaurentArithmetic ArithmeticCost HomologicalComplex
universe u
variable {K : Type u} [Field K] [DecidableEq K]
  {D c n p e rel h h₀ length : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def completeInitialCost (D c n p e h : ℕ) : ℕ :=
  Initial.initialCost D c n p e h +
  (n*(n+p)*c*boxSize D (Initial.radius2 h)*(2*boxSize D h+1) +
   n*(n+p)*boxSize D (Initial.radius2 h) +
   p*(n+p)*c*boxSize D (Initial.radius2 h)*(2*boxSize D h+1) +
   p*(n+p)*boxSize D (Initial.radius2 h) +
   e*(n+p)*n*boxSize D (Initial.radius3 h)*(2*boxSize D h+1))

omit [DecidableEq K] in
theorem completeInitial_cost (i : Initial.Inputs K D c n p e rel h) :
    i.runComplete.cost = completeInitialCost D c n p e h := by
  rw [Initial.Inputs.runComplete_cost,Initial.Inputs.run_cost,Initial.Inputs.makeForward_cost]
  rfl

def firstBox (D c n p e h : ℕ) : ℕ :=
  max (Initial.radius5 h)
    (stageLiftBox D (n+p) (n+p) (c+(e+p)) (Initial.radius5 h) +
      stageLiftBox D (n+p) (n+p) (c+(e+p)) (Initial.radius5 h))

def runBox (F : DenseTower K D h₀ length n) (G : DenseTower K D h₀ length c) (p e h : ℕ) : ℕ :=
  F.outputBox G (c+(e+p)) (n+p) (firstBox D c n p e h) + (Initial.radius5 h+Initial.radius5 h)

omit [Field K] [DecidableEq K] in
theorem runBox_ge_input (F : DenseTower K D h₀ length n) (G : DenseTower K D h₀ length c) (p e h : ℕ) :
    h ≤ runBox F G p e h := by
  dsimp [runBox,Initial.radius5,Initial.radius4,Initial.radius3,Initial.radius2]
  omega

def remainingCost (F : DenseTower K D h₀ length n) (G : DenseTower K D h₀ length c)
    (p e rel h : ℕ) : ℕ :=
  ((liftSolveCost D (n+p) rel (n+p) (c+(e+p)) (Initial.radius5 h) +
    liftSolveCost D (n+p) rel (c+(e+p)) (n+p) (Initial.radius5 h)) +
    DenseTower.updateCost D n c p (e+p)
      (stageLiftBox D (n+p) (n+p) (c+(e+p)) (Initial.radius5 h)) +
    F.costBound G (c+(e+p)) (n+p) (firstBox D c n p e h)) +
    absorbCost D n c p (e+p) (n+(F.ranks G).2) (c+(F.ranks G).1) (Initial.radius5 h)
      (F.outputBox G (c+(e+p)) (n+p) (firstBox D c n p e h)) (Initial.radius5 h)

theorem runInitial_cost (i : Initial.Inputs K D c n p e rel h)
    (F : DenseTower K D h₀ length n) (G : DenseTower K D h₀ length c)
    (hh : h₀ ≤ Initial.radius5 h)
    (hs : (initialStage i.runComplete.value.initial).Solvable)
    (hv : StateValid F G (firstUpdate (identityDense K D (Initial.radius5 h) p)
      i.runComplete.value.initial.complementProjector
      (solvePresentedStage (initialStage i.runComplete.value.initial) hs).value.1
      (solvePresentedStage (initialStage i.runComplete.value.initial) hs).value.2.1).value) :
    (runInitial i F G hh hs hv).cost ≤
      completeInitialCost D c n p e h+remainingCost F G p e rel h := by
  rw [runInitial,Work.bind_cost,completeInitial_cost]
  apply Nat.add_le_add_left
  exact stableCheckProgram_cost (initialStage i.runComplete.value.initial)
    i.runComplete.value.initial.complementProjector i.runComplete.value.forward i.runComplete.value.initial.beta
    F G hh hs hv

variable {C T : CochainComplex (ModuleCat.{u} (Laurent K D)) ℤ} {totalC totalT : ℕ}

theorem runNative_cost (cC : StableFree.Coordinates C) (cT : StableFree.Coordinates T)
    (frameC : AlgorithmTwoFiniteComplex.Coordinates C totalC) (frameT : AlgorithmTwoFiniteComplex.Coordinates T totalT)
    (sC : TermSelectors cC.rank totalC) (sT : TermSelectors cT.rank totalT)
    (hC : FrameRealizes cC frameC sC) (hT : FrameRealizes cT frameT sT)
    (equiv : HomotopyEquiv C T) (arrays : NativeArrays K D totalC totalT h)
    (ha : NativeRealizes frameC frameT equiv arrays) (l : ℕ)
    [C.IsGE 1] [T.IsGE 1] [C.IsStrictlyGE (-(l:ℤ))] [T.IsStrictlyGE (-(l:ℤ))] :
    (runNative cC cT frameC frameT sC sT hC hT equiv arrays ha l).cost ≤
      (cC.rank 1*cC.rank 2+cT.rank 1*cT.rank 2)*boxSize D h +
      (completeInitialCost D (cC.rank 1) (cT.rank 1) (cC.rank 2) (cT.rank 2) h +
        remainingCost (tailTower sT arrays.differentialT (l+1)) (tailTower sC arrays.differentialC (l+1))
          (cC.rank 2) (cT.rank 2) (cT.rank 0) h) := by
  rw [runNative,Work.bind_cost,extractInputs_cost]
  apply Nat.add_le_add_left
  apply runInitial_cost

end Decoupling.HighDim.StableFree.Effective.CochainProgram
