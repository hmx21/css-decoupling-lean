import Decoupling.HighDim.LaurentArithmeticData

/-!
# HD012 executable Laurent arithmetic with actual field-operation traces

Dense arrays are materialized exactly once. Convolution visits one input
box for each output coefficient. The semantic theorems identify the
output with the genuine Laurent sum/product; the cost counts the field
operations actually executed, including additions of zero coefficients.
-/
namespace Decoupling.HighDim.LaurentArithmetic
open ArithmeticCost
variable {K : Type*} [Field K] {D a b : ℕ}
set_option backward.isDefEq.respectTransparency false

def addProgram (v : Dense K D a) (w : Dense K D b) : Work K (Dense K D (max a b)) :=
  collect (boxSize D (max a b)) fun k =>
    ArithmeticCost.add (lookup v (exponentAt D (max a b) k))
      (lookup w (exponentAt D (max a b) k))

def negProgram (v : Dense K D a) : Work K (Dense K D a) :=
  collect (boxSize D a) fun k => ArithmeticCost.neg v[k]

def mulProgram (v : Dense K D a) (w : Dense K D b) : Work K (Dense K D (a + b)) :=
  collect (boxSize D (a + b)) fun k =>
    ArithmeticCost.dot (boxSize D a) (fun j => v[j])
      (fun j => lookup w (-exponentAt D a j + exponentAt D (a + b) k))

@[simp] theorem addProgram_cost (v : Dense K D a) (w : Dense K D b) :
    (addProgram v w).cost = boxSize D (max a b) := by
  simp [addProgram]

@[simp] theorem negProgram_cost (v : Dense K D a) :
    (negProgram v).cost = boxSize D a := by
  simp [negProgram]

@[simp] theorem mulProgram_cost (v : Dense K D a) (w : Dense K D b) :
    (mulProgram v w).cost = 2 * boxSize D (a + b) * boxSize D a := by
  simp [mulProgram]
  ring

theorem addProgram_correct (v : Dense K D a) (w : Dense K D b) :
    denote (addProgram v w).value = denote v + denote w := by
  apply denote_eq_of_coeff
  · exact LaurentBoxes.supported_add
      (LaurentBoxes.supported_mono (denote_supported v) (le_max_left _ _))
      (LaurentBoxes.supported_mono (denote_supported w) (le_max_right _ _))
  · intro k
    simp [addProgram, denote_coeff]

theorem negProgram_correct (v : Dense K D a) :
    denote (negProgram v).value = -denote v := by
  apply denote_eq_of_coeff
  · exact LaurentBoxes.supported_neg (denote_supported v)
  · intro k
    simp [negProgram, denote_coeff]

theorem denote_mul_coeff (v : Dense K D a) (w : Dense K D b) (x : Translation D) :
    (denote v * denote w).coeff x =
      ∑ j : Fin (boxSize D a), v[j] * lookup w (-exponentAt D a j + x) := by
  classical
  rw [denote, Finset.sum_mul]
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single_mul_apply, denote_coeff]

theorem mulProgram_correct (v : Dense K D a) (w : Dense K D b) :
    denote (mulProgram v w).value = denote v * denote w := by
  apply denote_eq_of_coeff
  · exact LaurentBoxes.supported_mul (denote_supported v) (denote_supported w)
  · intro k
    simp [mulProgram, denote_mul_coeff]

end Decoupling.HighDim.LaurentArithmetic
