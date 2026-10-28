import Decoupling.HighDim.LaurentArithmeticMatrix
import Decoupling.HighDim.CircuitSize

/-!
# HD012 explicit SUM lists from dense Laurent shear coefficients

The executable word contains one layer per stored coefficient, including
zeros. It requires no support search, arbitrary basis, or classical
choice of a factorization. Its actual matrix action and exact length are
proved from the input array.
-/
namespace Decoupling.HighDim.DenseShearCompile
open Matrix Circuit LaurentArithmetic
variable {K : Type*} [Field K] {D m n h : ℕ}
set_option backward.isDefEq.respectTransparency false

def index : Fin (m * (n * boxSize D h)) ≃ (Fin m × (Fin n × Fin (boxSize D h))) :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv.symm)

def gateAt (A : DenseMatrix K D m n h) (k : Fin (m * (n * boxSize D h))) :
    SUM K D (Fin m ⊕ Fin n) where
  control := Sum.inr (index k).2.1
  target := Sum.inl (index k).1
  displacement := exponentAt D h (index k).2.2
  weight := A[(index k).1][(index k).2.1][(index k).2.2]
  distinct := Sum.inr_ne_inl

def upperWord (A : DenseMatrix K D m n h) : List (SUM K D (Fin m ⊕ Fin n)) :=
  List.ofFn (gateAt A)

omit [Field K] in
@[simp] theorem upperWord_length (A : DenseMatrix K D m n h) :
    (upperWord A).length = m * n * boxSize D h := by
  simp [upperWord, mul_assoc]

noncomputable def term (A : DenseMatrix K D m n h) (k : Fin (m * (n * boxSize D h))) :
    Matrix (Fin m) (Fin n) (Laurent K D) :=
  Matrix.single (index k).1 (index k).2.1
    (AddMonoidAlgebra.single (exponentAt D h (index k).2.2)
      A[(index k).1][(index k).2.1][(index k).2.2])

theorem gateAt_action (A : DenseMatrix K D m n h) (k : Fin (m * (n * boxSize D h))) :
    (gateAt A k).xMatrix = Circuit.upper (term A k) := by
  exact Circuit.upperGate_xMatrix (index k).1 (index k).2.1
    (exponentAt D h (index k).2.2) A[(index k).1][(index k).2.1][(index k).2.2]

theorem terms_sum (A : DenseMatrix K D m n h) :
    ∑ k, term A k = matrixDenote A := by
  classical
  rw [← (index (D := D) (m := m) (n := n) (h := h)).symm.sum_comp]
  simp only [term, Equiv.apply_symm_apply, Fintype.sum_prod_type]
  funext i j
  simp [Matrix.sum_apply, Matrix.single_apply, matrixDenote, denote, ite_and]

private theorem list_action {α : Type*}
    (v : α → SUM K D (Fin m ⊕ Fin n))
    (a : α → Matrix (Fin m) (Fin n) (Laurent K D))
    (hv : ∀ x, (v x).xMatrix = Circuit.upper (a x)) (l : List α) :
    Circuit.xAction (l.map v) = Circuit.upper ((l.map a).sum) := by
  induction l with
  | nil => simp
  | cons x l ih => simp [Circuit.xAction_cons, hv, ih, Circuit.upper_add]

theorem upperWord_action (A : DenseMatrix K D m n h) :
    Circuit.xAction (upperWord A) = Circuit.upper (matrixDenote A) := by
  have hl := list_action (gateAt A) (term A) (gateAt_action A)
    (List.ofFn (id : Fin (m * (n * boxSize D h)) → Fin (m * (n * boxSize D h))))
  simpa only [List.map_ofFn, Function.comp_id, List.sum_ofFn, terms_sum, upperWord] using hl

end Decoupling.HighDim.DenseShearCompile
