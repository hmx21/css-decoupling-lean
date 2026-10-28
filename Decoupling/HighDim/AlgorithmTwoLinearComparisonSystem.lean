import Decoupling.HighDim.MatrixLinearSystems

/-!
# Actual finite scalar equations for comparison maps and contractions

HD012 Algorithm 2. These are exact algebraic encodings of
`L X + X R = Y`, prescribed values `X P = Q`, and entry masks.
They do not assert solvability. The executable compiler and native
cochain reconstruction are supplied in subsequent modules.
-/
namespace Decoupling.HighDim.AlgorithmTwoLinearComparison
open Matrix
noncomputable section
variable {R : Type*} [CommRing R] {n m k : ℕ}

abbrev Unknown (n m : ℕ) := Fin n × Fin m
abbrev Equation (n m k : ℕ) := (Fin n × Fin m) ⊕ ((Fin n × Fin k) ⊕ (Fin n × Fin m))

/-- Scalar coefficient of the actual rectangular Sylvester equation. -/
def sylvesterCoefficient (L : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin m) (Fin m) R) :
    Matrix (Unknown n m) (Unknown n m) R :=
  fun ij ab => (if ab.2 = ij.2 then L ij.1 ab.1 else 0) +
    (if ab.1 = ij.1 then A ab.2 ij.2 else 0)

theorem sylvesterCoefficient_mulVec (L : Matrix (Fin n) (Fin n) R)
    (A : Matrix (Fin m) (Fin m) R) (X : Matrix (Fin n) (Fin m) R) :
    sylvesterCoefficient L A *ᵥ (fun ij => X ij.1 ij.2) =
      fun ij => (L * X + X * A) ij.1 ij.2 := by
  funext ij
  simp only [sylvesterCoefficient, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    add_mul, Finset.sum_add_distrib, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  · simp
  · rw [Finset.sum_comm]
    simp [mul_comm]

/-- Scalar coefficient of prescribed values on a finite column family. -/
def valuesCoefficient (P : Matrix (Fin m) (Fin k) R) :
    Matrix (Fin n × Fin k) (Unknown n m) R :=
  fun ij ab => if ab.1 = ij.1 then P ab.2 ij.2 else 0

theorem valuesCoefficient_mulVec (P : Matrix (Fin m) (Fin k) R)
    (X : Matrix (Fin n) (Fin m) R) :
    valuesCoefficient P *ᵥ (fun ij => X ij.1 ij.2) = fun ij => (X * P) ij.1 ij.2 := by
  funext ij
  simp [valuesCoefficient, Matrix.mulVec, dotProduct, Fintype.sum_prod_type,
    Matrix.mul_apply, mul_comm]

/-- A false mask requires the corresponding unknown entry to vanish. -/
def maskCoefficient (allowed : Fin n → Fin m → Bool) :
    Matrix (Unknown n m) (Unknown n m) R :=
  fun ij ab => if allowed ij.1 ij.2 then 0 else if ab = ij then 1 else 0

theorem maskCoefficient_mulVec (allowed : Fin n → Fin m → Bool)
    (X : Matrix (Fin n) (Fin m) R) :
    maskCoefficient allowed *ᵥ (fun ij => X ij.1 ij.2) =
      fun ij => if allowed ij.1 ij.2 then 0 else X ij.1 ij.2 := by
  funext ij
  simp [maskCoefficient, Matrix.mulVec, dotProduct, Finset.sum_ite_irrel]

/-- The combined scalar system, without a boundedness or solution oracle. -/
def systemMatrix (L : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin m) (Fin m) R)
    (P : Matrix (Fin m) (Fin k) R) (allowed : Fin n → Fin m → Bool) :
    Matrix (Equation n m k) (Unknown n m) R :=
  Sum.elim (sylvesterCoefficient L A) (Sum.elim (valuesCoefficient P) (maskCoefficient allowed))

def systemRhs (Y : Matrix (Fin n) (Fin m) R) (Q : Matrix (Fin n) (Fin k) R) :
    Equation n m k → R :=
  Sum.elim (fun ij => Y ij.1 ij.2) (Sum.elim (fun ij => Q ij.1 ij.2) (fun _ => 0))

def Satisfies (L : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin m) (Fin m) R)
    (P : Matrix (Fin m) (Fin k) R) (allowed : Fin n → Fin m → Bool)
    (Y : Matrix (Fin n) (Fin m) R) (Q : Matrix (Fin n) (Fin k) R)
    (X : Matrix (Fin n) (Fin m) R) : Prop :=
  L * X + X * A = Y ∧ X * P = Q ∧ ∀ i j, allowed i j = false → X i j = 0

theorem system_equation_iff (L : Matrix (Fin n) (Fin n) R) (A : Matrix (Fin m) (Fin m) R)
    (P : Matrix (Fin m) (Fin k) R) (allowed : Fin n → Fin m → Bool)
    (Y : Matrix (Fin n) (Fin m) R) (Q : Matrix (Fin n) (Fin k) R)
    (X : Matrix (Fin n) (Fin m) R) :
    systemMatrix L A P allowed *ᵥ (fun ij => X ij.1 ij.2) = systemRhs Y Q ↔
      Satisfies L A P allowed Y Q X := by
  have hs := sylvesterCoefficient_mulVec L A X
  have hp := valuesCoefficient_mulVec P X
  have hm := maskCoefficient_mulVec allowed X
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · funext i j
      exact (congrFun hs (i,j)).symm.trans (congrFun h (.inl (i,j)))
    · funext i j
      exact (congrFun hp (i,j)).symm.trans (congrFun h (.inr (.inl (i,j))))
    · intro i j hij
      have he := (congrFun hm (i,j)).symm.trans (congrFun h (.inr (.inr (i,j))))
      simpa [hij, systemRhs] using he
  · rintro ⟨hS, hP, hM⟩
    funext row
    rcases row with ij | (ij | ij)
    · exact (congrFun hs ij).trans (congrFun (congrFun hS ij.1) ij.2)
    · exact (congrFun hp ij).trans (congrFun (congrFun hP ij.1) ij.2)
    · change (maskCoefficient allowed *ᵥ (fun ij => X ij.1 ij.2)) ij = 0
      rw [hm]
      cases ha : allowed ij.1 ij.2 <;> simp [ha, hM]

end
end Decoupling.HighDim.AlgorithmTwoLinearComparison
