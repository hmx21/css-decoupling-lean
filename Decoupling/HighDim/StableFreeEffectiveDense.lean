import Decoupling.HighDim.StableFreeLiftSystem
import Decoupling.HighDim.LaurentArithmeticStructural

/-!
# Executable dense assembly of the projective-lift equations

Known coefficient arrays are materialized once. Only `-D`, `E-I`, and
`G-I` perform field operations; the expanded scalar-system entries are
then copied with canonical finite sum/product index enumerations. This
records actual operations, not a freely assigned assembly-cost certificate.
-/

namespace Decoupling.HighDim.StableFree.Effective

open Matrix ArithmeticCost LaurentArithmetic
variable {K : Type*} [Field K] {D b v rel k l : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

def zeroDense (K : Type*) [Zero K] (D b : ℕ) : Dense K D b :=
  Vector.ofFn (fun _ => 0)

def oneDense (K : Type*) [Zero K] [One K] (D b : ℕ) : Dense K D b :=
  Vector.ofFn (fun i => if exponentAt D b i = 0 then 1 else 0)

theorem zeroDense_correct : denote (zeroDense K D b) = 0 := by
  apply denote_eq_of_coeff
  · exact LaurentBoxes.supported_zero
  · intro i
    simp [zeroDense]

theorem oneDense_correct : denote (oneDense K D b) = 1 := by
  apply denote_eq_of_coeff
  · exact LaurentBoxes.supported_one
  · intro i
    simp [oneDense, AddMonoidAlgebra.one_def, Finsupp.single_apply, eq_comm]

def identityDense (K : Type*) [Zero K] [One K] (D b k : ℕ) : DenseMatrix K D k k b :=
  Vector.ofFn (fun i => Vector.ofFn (fun j => if i=j then oneDense K D b else zeroDense K D b))

theorem identityDense_correct : matrixDenote (identityDense K D b k) = 1 := by
  funext i j
  simp only [matrixDenote, identityDense, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta]
  split
  · next h => subst j; rw [oneDense_correct]; simp
  · next h => rw [zeroDense_correct]; simp [Matrix.one_apply_ne h]

/-- Subtract two arrays in their common box, counting each actual subtraction. -/
def subtractDense (x y : Dense K D b) : Work K (Dense K D b) :=
  collect (boxSize D b) (fun i => ArithmeticCost.sub x[i] y[i])

@[simp] theorem subtractDense_cost (x y : Dense K D b) :
    (subtractDense x y).cost = boxSize D b := by simp [subtractDense]

theorem subtractDense_correct (x y : Dense K D b) :
    denote (subtractDense x y).value = denote x - denote y := by
  apply denote_eq_of_coeff
  · exact LaurentBoxes.supported_sub (denote_supported x) (denote_supported y)
  · intro i
    simp [subtractDense, denote_coeff]

def subtractIdentityProgram (E : DenseMatrix K D k k b) : Work K (DenseMatrix K D k k b) :=
  collect k fun i => collect k fun j => subtractDense E[i][j] (identityDense K D b k)[i][j]

@[simp] theorem subtractIdentityProgram_cost (E : DenseMatrix K D k k b) :
    (subtractIdentityProgram E).cost = k*k*boxSize D b := by
  simp [subtractIdentityProgram, Nat.mul_assoc]

theorem subtractIdentityProgram_correct (E : DenseMatrix K D k k b) :
    matrixDenote (subtractIdentityProgram E).value = matrixDenote E - 1 := by
  rw [← identityDense_correct (K := K) (D := D) (b := b) (k := k)]
  funext i j
  change denote ((subtractIdentityProgram E).value[i][j]) = _
  simp only [subtractIdentityProgram, collect_value_get, subtractDense_correct]
  rfl

/-- Fixed integer-index enumerations; no field tests or basis choices occur. -/
def liftRowEnumeration (v k l : ℕ) : LiftRows v k l ≃ Fin ((v+(k+k))*l) :=
  (Equiv.prodCongr
    ((Equiv.sumCongr (Equiv.refl (Fin v)) (finSumFinEquiv : Fin k ⊕ Fin k ≃ Fin (k+k))).trans
      (finSumFinEquiv : Fin v ⊕ Fin (k+k) ≃ Fin (v+(k+k))))
    (Equiv.refl (Fin l))).trans finProdFinEquiv

def liftUnknownEnumeration (k rel l : ℕ) : LiftUnknowns k rel l ≃ Fin ((k+rel)*l) :=
  (Equiv.prodCongr (finSumFinEquiv : Fin k ⊕ Fin rel ≃ Fin (k+rel))
    (Equiv.refl (Fin l))).trans finProdFinEquiv

/-- A pure block-copying formula, used for both coefficient arrays and semantics. -/
def coefficientBlocks {S : Type*} (zero : S)
    (A : Matrix (Fin v) (Fin k) S) (Dneg : Matrix (Fin v) (Fin rel) S)
    (Eminus : Matrix (Fin k) (Fin k) S) (Gminus : Matrix (Fin l) (Fin l) S) :
    Matrix (LiftRows v k l) (LiftUnknowns k rel l) S := fun ij ab =>
  match ij.1,ab.1 with
  | .inl i,.inl a => if ab.2=ij.2 then A i a else zero
  | .inl i,.inr a => if ab.2=ij.2 then Dneg i a else zero
  | .inr (.inl i),.inl a => if ab.2=ij.2 then Eminus i a else zero
  | .inr (.inl _),.inr _ => zero
  | .inr (.inr i),.inl a => if a=i then Gminus ab.2 ij.2 else zero
  | .inr (.inr _),.inr _ => zero

theorem coefficientBlocks_eq {R : Type*} [CommRing R]
    (A : Matrix (Fin v) (Fin k) R) (F : Matrix (Fin v) (Fin rel) R)
    (E : Matrix (Fin k) (Fin k) R) (G : Matrix (Fin l) (Fin l) R) :
    coefficientBlocks 0 A (-F) (E-1) (G-1) = liftCoefficients A F E G := rfl

def assembleLiftCoefficients
    (A : DenseMatrix K D v k b) (Dneg : DenseMatrix K D v rel b)
    (Eminus : DenseMatrix K D k k b) (Gminus : DenseMatrix K D l l b) :
    DenseMatrix K D ((v+(k+k))*l) ((k+rel)*l) b :=
  Vector.ofFn fun i => Vector.ofFn fun j =>
    coefficientBlocks (zeroDense K D b) (fun i j => A[i][j]) (fun i j => Dneg[i][j])
      (fun i j => Eminus[i][j]) (fun i j => Gminus[i][j])
      ((liftRowEnumeration v k l).symm i) ((liftUnknownEnumeration k rel l).symm j)

theorem assembleLiftCoefficients_correct
    (A : DenseMatrix K D v k b) (Dneg : DenseMatrix K D v rel b)
    (Eminus : DenseMatrix K D k k b) (Gminus : DenseMatrix K D l l b) :
    matrixDenote (assembleLiftCoefficients A Dneg Eminus Gminus) =
      (coefficientBlocks 0 (matrixDenote A) (matrixDenote Dneg)
        (matrixDenote Eminus) (matrixDenote Gminus)).submatrix
          (liftRowEnumeration v k l).symm (liftUnknownEnumeration k rel l).symm := by
  funext i j
  simp only [matrixDenote, assembleLiftCoefficients, Fin.getElem_fin,
    Vector.getElem_ofFn, Fin.eta, Matrix.submatrix_apply]
  rcases (liftRowEnumeration v k l).symm i with ⟨a|a|a,c⟩ <;>
    rcases (liftUnknownEnumeration k rel l).symm j with ⟨x|x,y⟩ <;>
    simp only [coefficientBlocks]
  all_goals first
    | (split <;> first | rfl | exact zeroDense_correct)
    | exact zeroDense_correct

/-- The executable compiler materializes the three changed blocks once. -/
def liftSystemProgram
    (A : DenseMatrix K D v k b) (F : DenseMatrix K D v rel b)
    (E : DenseMatrix K D k k b) (G : DenseMatrix K D l l b) :
    Work K (DenseMatrix K D ((v+(k+k))*l) ((k+rel)*l) b) :=
  Work.bind (matrixNegProgram F) fun Fneg =>
    Work.bind (subtractIdentityProgram E) fun Eminus =>
      Work.bind (subtractIdentityProgram G) fun Gminus =>
        Work.pure (assembleLiftCoefficients A Fneg Eminus Gminus)

@[simp] theorem liftSystemProgram_cost
    (A : DenseMatrix K D v k b) (F : DenseMatrix K D v rel b)
    (E : DenseMatrix K D k k b) (G : DenseMatrix K D l l b) :
    (liftSystemProgram A F E G).cost = (v*rel+k*k+l*l)*boxSize D b := by
  simp only [liftSystemProgram, Work.bind_cost, matrixNegProgram_cost,
    subtractIdentityProgram_cost, Work.pure_cost]
  ring

theorem liftSystemProgram_correct
    (A : DenseMatrix K D v k b) (F : DenseMatrix K D v rel b)
    (E : DenseMatrix K D k k b) (G : DenseMatrix K D l l b) :
    matrixDenote (liftSystemProgram A F E G).value =
      (liftCoefficients (matrixDenote A) (matrixDenote F) (matrixDenote E) (matrixDenote G)).submatrix
        (liftRowEnumeration v k l).symm (liftUnknownEnumeration k rel l).symm := by
  simp only [liftSystemProgram, Work.bind_value, Work.pure_value,
    assembleLiftCoefficients_correct, matrixNegProgram_correct,
    subtractIdentityProgram_correct, coefficientBlocks_eq]

/-- The right side is copied into the first block and zero elsewhere. -/
def liftRightDense (B : DenseMatrix K D v l b) : Vector (Dense K D b) ((v+(k+k))*l) :=
  Vector.ofFn fun i =>
    let j := (liftRowEnumeration v k l).symm i
    Sum.elim (fun r => B[r][j.2]) (fun _ => zeroDense K D b) j.1

private theorem liftRightEntry_correct (B : DenseMatrix K D v l b) (j : LiftRows v k l) :
    denote (Sum.elim (fun r => B[r][j.2]) (fun _ => zeroDense K D b) j.1) =
      liftStack (matrixDenote B) 0 0 j := by
  rcases j with ⟨i|i|i,t⟩ <;> first | rfl | exact zeroDense_correct

theorem liftRightDense_correct (B : DenseMatrix K D v l b) :
    (fun i => denote (liftRightDense (k := k) B)[i]) =
      (liftStack (matrixDenote B) 0 0) ∘ (liftRowEnumeration v k l).symm := by
  funext i
  simpa only [liftRightDense, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Function.comp_apply]
    using liftRightEntry_correct B ((liftRowEnumeration v k l).symm i)

end Decoupling.HighDim.StableFree.Effective
