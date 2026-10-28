import Decoupling.HighDim.StableFreeEffectiveInitialCost
import Decoupling.HighDim.StableFreeEffectiveInitialForward

/-! # HD012 counted forward presentation lift and both initial directions -/
namespace Decoupling.HighDim.StableFree.Effective.Initial
open Matrix ArithmeticCost LaurentArithmetic CategoryTheory
variable {K : Type*} [Field K] {D c n p e rel h : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

structure CompleteOutput (K : Type*) (D c n p e rel H : ℕ) where
  initial : Output K D c n p e rel H
  forward : DenseMatrix K D (c+(e+p)) (n+p) H

namespace Inputs
variable (i : Inputs K D c n p e rel h)

def makeForward : Work K (DenseMatrix K D (c+(e+p)) (n+p) (radius5 h)) :=
  let rho := joinColumns i.G i.Z
  Work.bind (matrixMulProgram i.F rho) fun FR =>
    Work.bind (subSame (joinColumns (identityDense K D (radius2 h) n)
      (zeroMatrix K D n p (radius2 h))) FR) fun qN =>
      Work.bind (matrixMulProgram i.X rho) fun XR =>
        Work.bind (subSame (joinColumns (zeroMatrix K D p n (radius2 h))
          (identityDense K D (radius2 h) p)) XR) fun qP =>
          Work.bind (matrixMulProgram i.Y qN) fun YqN =>
            Work.pure (matrixPad (rows (matrixPad rho (radius3 h))
              (rows YqN (matrixPad qP (radius3 h)))) (radius5 h))

def runComplete : Work K (CompleteOutput K D c n p e rel (radius5 h)) :=
  Work.bind i.run fun base =>
    Work.bind i.makeForward fun F => Work.pure ⟨base,F⟩

theorem makeForward_cost :
    i.makeForward.cost =
      n*(n+p)*c*boxSize D (radius2 h)*(2*boxSize D h+1) + n*(n+p)*boxSize D (radius2 h) +
      p*(n+p)*c*boxSize D (radius2 h)*(2*boxSize D h+1) + p*(n+p)*boxSize D (radius2 h) +
      e*(n+p)*n*boxSize D (radius3 h)*(2*boxSize D h+1) := by
  simp only [makeForward, Work.bind_cost, matrixMulProgram_cost, subSame_cost, Work.pure_cost]
  dsimp only [radius3, radius2]
  omega

theorem runComplete_cost : i.runComplete.cost = i.run.cost + i.makeForward.cost := by
  simp [runComplete]

end Inputs

variable {M N : ModuleCat (Laurent K D)}

theorem makeForward_correct (i : Inputs K D c n p e rel h) (a : Data M N c n p e rel)
    (hi : Realizes i a) :
    matrixDenote i.makeForward.value = a.matrixForward := by
  simp only [Inputs.makeForward, Work.bind_value, Work.pure_value]
  rw [matrixPad_correct _ (by dsimp [radius5,radius4,radius3,radius2]; omega),
    rows_correct, rows_correct,
    matrixPad_correct _ (by dsimp [radius3,radius2]; omega),
    matrixPad_correct _ (by dsimp [radius3,radius2]; omega)]
  simp only [cols_correct, matrixMulProgram_correct, subSame_correct,
    identityDense_correct, zeroMatrix_correct, hi.F, hi.G, hi.X, hi.Y, hi.Z]
  rfl

end Decoupling.HighDim.StableFree.Effective.Initial
