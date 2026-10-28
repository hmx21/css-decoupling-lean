import Decoupling.HighDim.AlgorithmTwoToricDataIndex
import Decoupling.HighDim.AlgorithmTwoToricDataFaces
import Decoupling.HighDim.LaurentArithmeticMatrix

/-!
# Materialised toric differential and top-column arrays

The only field operation is computing minus one once. All entries
then select zero, one, or this cached minus one using integer subset,
parity, and exponent tests. In particular, no polynomial arithmetic
or field power is hidden in matrix assembly.
-/
namespace Decoupling.HighDim.AlgorithmTwoToricData
open ArithmeticCost
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

def unitExponent (D : ℕ) (i : Fin D) : Translation D := fun j => if j = i then 1 else 0

theorem unitExponent_eq {D : ℕ} (i : Fin D) : unitExponent D i = translationBasis i := by
  funext j
  simp [unitExponent, translationBasis, Pi.single_apply]

variable {K : Type} [Field K]

def faceCoefficient (minusOne : K) {D : ℕ} (row col : Finset (Fin D)) (a : Translation D) : K :=
  match removedDirection row col with
  | none => 0
  | some i =>
    if a = unitExponent D i then cachedSign minusOne (cellPosition col i)
    else if a = 0 then cachedSign minusOne (cellPosition col i + 1) else 0

def faceDense (minusOne : K) {D : ℕ} (row col : Finset (Fin D)) :
    LaurentArithmetic.Dense K D 1 :=
  Vector.ofFn (fun a => faceCoefficient minusOne row col (LaurentArithmetic.exponentAt D 1 a))

def differentialArray (D : ℕ) (t : Vector ℕ (D - 1)) (minusOne : K) :
    LaurentArithmetic.DenseMatrix K D (totalRank D t) (totalRank D t) 1 :=
  Vector.ofFn fun r => Vector.ofFn fun c =>
    let row := labelEquiv D t r
    let col := labelEquiv D t c
    if row.1 = col.1 then faceDense minusOne (subsetAt D row.2) (subsetAt D col.2)
    else Vector.replicate (LaurentArithmetic.boxSize D 1) 0

/-- Actual trace-producing target builder. -/
def differentialProgram (D : ℕ) (t : Vector ℕ (D - 1)) :
    Work K (LaurentArithmetic.DenseMatrix K D (totalRank D t) (totalRank D t) 1) :=
  Work.bind (ArithmeticCost.neg (1 : K)) fun minusOne => Work.pure (differentialArray D t minusOne)

@[simp] theorem differentialProgram_value (D : ℕ) (t : Vector ℕ (D - 1)) :
    (differentialProgram (K := K) D t).value = differentialArray D t (-1 : K) := rfl

@[simp] theorem differentialProgram_cost (D : ℕ) (t : Vector ℕ (D - 1)) :
    (differentialProgram (K := K) D t).cost = 1 := by simp [differentialProgram]

/-- Empty-cell unit columns; no field arithmetic is required. -/
def topArray (D : ℕ) (t : Vector ℕ (D - 1)) :
    LaurentArithmetic.DenseMatrix K D (totalRank D t) (copyCount D t) 0 :=
  Vector.ofFn fun r => Vector.ofFn fun c => Vector.ofFn fun _ =>
    if r = topLabel D t (copyEquiv D t c) then 1 else 0

def topProgram (D : ℕ) (t : Vector ℕ (D - 1)) :
    Work K (LaurentArithmetic.DenseMatrix K D (totalRank D t) (copyCount D t) 0) :=
  Work.pure (topArray D t)

@[simp] theorem topProgram_cost (D : ℕ) (t : Vector ℕ (D - 1)) :
    (topProgram (K := K) D t).cost = 0 := rfl

def topDegrees (D : ℕ) (t : Vector ℕ (D - 1)) : Vector ℤ (copyCount D t) :=
  Vector.ofFn (fun c => ((copyEquiv D t c).1.val : ℤ) + 1)

omit [Field K] in
@[simp] theorem topDegrees_get (D : ℕ) (t : Vector ℕ (D - 1)) (c : Fin (copyCount D t)) :
    (topDegrees D t).get c = ((copyEquiv D t c).1.val : ℤ) + 1 := by
  change (Vector.ofFn (fun a => ((copyEquiv D t a).1.val : ℤ) + 1))[c.val] = _
  simp

/-- Materialise both arrays once and retain their actual shared trace. -/
def targetProgram (D : ℕ) (t : Vector ℕ (D - 1)) :
    Work K (LaurentArithmetic.DenseMatrix K D (totalRank D t) (totalRank D t) 1 ×
      LaurentArithmetic.DenseMatrix K D (totalRank D t) (copyCount D t) 0) :=
  Work.bind (differentialProgram D t) fun d =>
    Work.bind (topProgram D t) fun z => Work.pure (d, z)

@[simp] theorem targetProgram_value (D : ℕ) (t : Vector ℕ (D - 1)) :
    (targetProgram (K := K) D t).value = (differentialArray D t (-1 : K), topArray D t) := rfl

@[simp] theorem targetProgram_cost (D : ℕ) (t : Vector ℕ (D - 1)) :
    (targetProgram (K := K) D t).cost = 1 := by simp [targetProgram]

end Decoupling.HighDim.AlgorithmTwoToricData
