import Decoupling.HighDim.StableFreeEffectiveInitialDense

/-!
# HD012 executable initial Schanuel matrix construction

The inputs are the actual stored matrices of the comparison, homotopy
errors and original relation map. Every multiplication, addition and
negation is performed by an already counted dense program. The largest
exponent radius here is exactly five times the common input radius.
-/
namespace Decoupling.HighDim.StableFree.Effective.Initial
open Matrix ArithmeticCost LaurentArithmetic
variable {K : Type*} [Field K] {D c n p e rel h : ℕ}

abbrev radius2 (h : ℕ) := h+h
abbrev radius3 (h : ℕ) := h+radius2 h
abbrev radius4 (h : ℕ) := h+radius3 h
abbrev radius5 (h : ℕ) := h+radius4 h

structure Inputs (K : Type*) (D c n p e rel h : ℕ) where
  F : DenseMatrix K D n c h
  G : DenseMatrix K D c n h
  X : DenseMatrix K D p c h
  Y : DenseMatrix K D e n h
  Z : DenseMatrix K D c p h
  T : DenseMatrix K D n e h
  relations : DenseMatrix K D n rel h

structure Output (K : Type*) (D c n p e rel H : ℕ) where
  alpha : DenseMatrix K D (n+p) (n+p) H
  beta : DenseMatrix K D (n+p) (c+(e+p)) H
  relations : DenseMatrix K D (n+p) rel H
  leftProjector : DenseMatrix K D (n+p) (n+p) H
  rightProjector : DenseMatrix K D (c+(e+p)) (c+(e+p)) H
  complementProjector : DenseMatrix K D (e+p) (e+p) H

namespace Inputs
variable (i : Inputs K D c n p e rel h)

def makeL : Work K (DenseMatrix K D n (e+p) (radius2 h)) :=
  Work.bind (matrixMulProgram i.F i.Z) fun FZ =>
    Work.bind (matrixNegProgram FZ) fun negFZ =>
      Work.pure (joinColumns (matrixPad i.T (radius2 h)) negFZ)

def makeR (L : DenseMatrix K D n (e+p) (radius2 h)) :
    Work K (DenseMatrix K D c (e+p) (radius3 h)) :=
  Work.bind (matrixMulProgram i.G L) fun gTimesL =>
    addSame gTimesL (matrixPad (joinColumns (zeroMatrix K D c e h) i.Z) (radius3 h))

def makeQN (L : DenseMatrix K D n (e+p) (radius2 h))
    (R : DenseMatrix K D c (e+p) (radius3 h)) :
    Work K (DenseMatrix K D n (e+p) (radius4 h)) :=
  Work.bind (matrixMulProgram i.F R) fun FR => subSame (matrixPad L (radius4 h)) FR

def makeQP (R : DenseMatrix K D c (e+p) (radius3 h)) :
    Work K (DenseMatrix K D p (e+p) (radius4 h)) :=
  Work.bind (matrixMulProgram i.X R) fun XR =>
    subSame (joinColumns (zeroMatrix K D p e (radius4 h))
      (identityDense K D (radius4 h) p)) XR

def makeQ (QN : DenseMatrix K D n (e+p) (radius4 h))
    (QP : DenseMatrix K D p (e+p) (radius4 h)) :
    Work K (DenseMatrix K D (e+p) (e+p) (radius5 h)) :=
  Work.bind (matrixMulProgram i.Y QN) fun YQN =>
    Work.pure (rows YQN (matrixPad QP (radius5 h)))

def makeOutput (QN : DenseMatrix K D n (e+p) (radius4 h))
    (QP : DenseMatrix K D p (e+p) (radius4 h))
    (Q : DenseMatrix K D (e+p) (e+p) (radius5 h)) :
    Output K D c n p e rel (radius5 h) where
  alpha := identityDense K D (radius5 h) (n+p)
  beta := matrixPad (rows
    (joinColumns (matrixPad i.F (radius4 h)) QN)
    (joinColumns (matrixPad i.X (radius4 h)) QP)) (radius5 h)
  relations := matrixPad (rows i.relations (zeroMatrix K D p rel h)) (radius5 h)
  leftProjector := identityDense K D (radius5 h) (n+p)
  rightProjector := rows
    (joinColumns (identityDense K D (radius5 h) c) (zeroMatrix K D c (e+p) (radius5 h)))
    (joinColumns (zeroMatrix K D (e+p) c (radius5 h)) Q)
  complementProjector := Q

def run : Work K (Output K D c n p e rel (radius5 h)) :=
  Work.bind i.makeL fun L =>
    Work.bind (i.makeR L) fun R =>
      Work.bind (i.makeQN L R) fun QN =>
        Work.bind (i.makeQP R) fun QP =>
          Work.bind (i.makeQ QN QP) fun Q =>
            Work.pure (i.makeOutput QN QP Q)

end Inputs
end Decoupling.HighDim.StableFree.Effective.Initial
