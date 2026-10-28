import Decoupling.HighDim.DenseShearCompile
import Decoupling.HighDim.LaurentArithmeticStructural

/-!
# HD012 executable signed shear circuit compilation

Negating a gate weight is a real counted field operation. Species
relabelling and integer displacement negation copy data without field
arithmetic. Both X and Z actions of the final explicit word are proved.
-/
namespace Decoupling.HighDim.DenseShearCompile
open Circuit LaurentArithmetic ArithmeticCost Matrix
variable {K : Type*} [Field K] {D m n a b : ℕ}
set_option backward.isDefEq.respectTransparency false

def lowerWord (A : DenseMatrix K D n m a) : List (SUM K D (Fin m ⊕ Fin n)) :=
  (upperWord A).map fun g => {
    control := (Equiv.sumComm (Fin n) (Fin m)) g.control
    target := (Equiv.sumComm (Fin n) (Fin m)) g.target
    displacement := g.displacement
    weight := g.weight
    distinct := fun h => g.distinct ((Equiv.sumComm _ _).injective h) }

omit [Field K] in
@[simp] theorem lowerWord_length (A : DenseMatrix K D n m a) :
    (lowerWord A).length = n * m * boxSize D a := by
  simp [lowerWord]

theorem lowerWord_action (A : DenseMatrix K D n m a) :
    Circuit.xAction (lowerWord A) = Circuit.lower (matrixDenote A) := by
  change Circuit.xAction ((upperWord A).map fun g => g.relabel (Equiv.sumComm _ _)) = _
  rw [Circuit.xAction_relabel, upperWord_action]
  funext i j
  cases i <;> cases j <;> rfl

def dualGateProgram {ι : Type*} (g : SUM K D ι) : Work K (SUM K D ι) :=
  Work.bind (ArithmeticCost.neg g.weight) fun c => Work.pure {
    control := g.target
    target := g.control
    displacement := -g.displacement
    weight := c
    distinct := Ne.symm g.distinct }

@[simp] theorem dualGateProgram_value {ι : Type*} (g : SUM K D ι) :
    (dualGateProgram g).value = g.dual := rfl

@[simp] theorem dualGateProgram_cost {ι : Type*} (g : SUM K D ι) :
    (dualGateProgram g).cost = 1 := rfl

def dualWordProgram {ι : Type*} : List (SUM K D ι) → Work K (List (SUM K D ι))
  | [] => Work.pure []
  | g :: l => Work.bind (dualGateProgram g) fun g' =>
      Work.bind (dualWordProgram l) fun l' => Work.pure (g' :: l')

@[simp] theorem dualWordProgram_value {ι : Type*} (l : List (SUM K D ι)) :
    (dualWordProgram l).value = l.map SUM.dual := by
  induction l with
  | nil => rfl
  | cons g l ih => simp [dualWordProgram, ih]

@[simp] theorem dualWordProgram_cost {ι : Type*} (l : List (SUM K D ι)) :
    (dualWordProgram l).cost = l.length := by
  induction l with
  | nil => rfl
  | cons g l ih => simp [dualWordProgram, ih, Nat.add_comm]

def twoShearProgram (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    Work K (List (SUM K D (Fin m ⊕ Fin n))) :=
  dualWordProgram (upperWord g ++ lowerWord f)

@[simp] theorem twoShearProgram_cost (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    (twoShearProgram f g).cost = m * n * boxSize D b + n * m * boxSize D a := by
  simp [twoShearProgram]

@[simp] theorem twoShearProgram_length (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    (twoShearProgram f g).value.length = m * n * boxSize D b + n * m * boxSize D a := by
  simp [twoShearProgram]

theorem twoShearProgram_action (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    Circuit.zAction (twoShearProgram f g).value =
      Circuit.upper (matrixDenote g) * Circuit.lower (matrixDenote f) := by
  rw [twoShearProgram, dualWordProgram_value, Circuit.zAction_dual,
    Circuit.xAction_append, upperWord_action, lowerWord_action]

/-- The source coordinates are identified with target coordinates by the
explicit block-swap equivalence. In these fixed physical species labels
the remaining permutation is identity, so the emitted word consists of
SUM layers. The equivalence is retained in the action statement. -/
def thetaProgram (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    Work K (List (Circuit.Layer K D (Fin n ⊕ Fin m))) :=
  Work.bind (matrixNegProgram g) fun ng =>
    Work.bind (twoShearProgram ng f) fun l => Work.pure (l.map Circuit.Layer.sum)

@[simp] theorem thetaProgram_cost (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    (thetaProgram f g).cost =
      n * m * boxSize D a + 2 * (m * n * boxSize D b) := by
  simp only [thetaProgram, Work.bind_cost, matrixNegProgram_cost, twoShearProgram_cost,
    Work.pure_cost, add_zero]
  omega

@[simp] theorem thetaProgram_length (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    (thetaProgram f g).value.length =
      n * m * boxSize D a + m * n * boxSize D b := by
  simp [thetaProgram]

theorem thetaProgram_z (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    Circuit.wordZ (thetaProgram f g).value =
      (Stabilization.theta (matrixDenote f) (matrixDenote g)).submatrix id
        (Equiv.sumComm (Fin m) (Fin n)).symm := by
  simp only [thetaProgram, Work.bind_value, Work.pure_value, Circuit.wordZ_sum]
  rw [twoShearProgram_action, matrixNegProgram_correct, Circuit.theta_reindexed]
  have he : (Equiv.sumComm (Fin m) (Fin n)).symm.trans (Equiv.sumComm (Fin m) (Fin n)) =
      Equiv.refl (Fin n ⊕ Fin m) := Equiv.symm_trans_self _
  rw [he]
  rw [show Circuit.permMatrix (K := K) (D := D) (Equiv.refl (Fin n ⊕ Fin m)) = 1 from rfl,
    Matrix.mul_one]

theorem thetaProgram_x (f : DenseMatrix K D n m a) (g : DenseMatrix K D m n b) :
    Circuit.wordX (thetaProgram f g).value =
      dagger ((Stabilization.theta (matrixDenote g) (matrixDenote f)).submatrix
        (Equiv.sumComm (Fin m) (Fin n)).symm id) := by
  apply Circuit.wordX_eq_dagger_inverse _ _ _ (thetaProgram_z f g)
  rw [Matrix.submatrix_mul_equiv, Stabilization.theta_mul_reverse, Matrix.submatrix_id_id]

end Decoupling.HighDim.DenseShearCompile
