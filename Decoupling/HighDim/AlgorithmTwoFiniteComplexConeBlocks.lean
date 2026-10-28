import Decoupling.HighDim.AlgorithmTwoFiniteComplexConeMatrix

/-! # Exact inverse and homotopy block equations of a solved cone contraction -/
namespace Decoupling.HighDim.AlgorithmTwoFiniteComplex
open Matrix
noncomputable section
variable {R : Type*} [CommRing R] {m n : ℕ}

def splitMatrix (H : Matrix (Fin (m+n)) (Fin (m+n)) R) : Matrix (Fin m ⊕ Fin n) (Fin m ⊕ Fin n) R :=
  H.submatrix finSumFinEquiv finSumFinEquiv

def inverseBlock (H : Matrix (Fin (m+n)) (Fin (m+n)) R) : Matrix (Fin m) (Fin n) R := (splitMatrix H).toBlocks₁₂

def sourceBlock (H : Matrix (Fin (m+n)) (Fin (m+n)) R) : Matrix (Fin m) (Fin m) R := (splitMatrix H).toBlocks₁₁

def targetBlock (H : Matrix (Fin (m+n)) (Fin (m+n)) R) : Matrix (Fin n) (Fin n) R := -(splitMatrix H).toBlocks₂₂

/-- All three equations use precisely the indicated blocks of the solved H. -/
theorem cone_blocks {R : Type} [CommRing R]
    (dT : Matrix (Fin m) (Fin m) R) (dC : Matrix (Fin n) (Fin n) R)
    (A : Matrix (Fin n) (Fin m) R) (H : Matrix (Fin (m+n)) (Fin (m+n)) R)
    (he : coneMatrix dT dC A * H + H * coneMatrix dT dC A = 1) :
    dT * inverseBlock H = inverseBlock H * dC ∧
      dT * sourceBlock H + sourceBlock H * dT = inverseBlock H * A - 1 ∧
      dC * targetBlock H + targetBlock H * dC = A * inverseBlock H - 1 := by
  let e : Fin m ⊕ Fin n ≃ Fin (m+n) := finSumFinEquiv
  have hc : (coneMatrix dT dC A).submatrix e e = Matrix.fromBlocks (-dT) 0 A dC := by
    funext i j
    simp [coneMatrix, Matrix.submatrix_apply, e]
  have hb := congrArg (fun X : Matrix (Fin (m+n)) (Fin (m+n)) R => X.submatrix e e) he
  simp only [Matrix.submatrix_add, Pi.add_apply] at hb
  rw [← Matrix.submatrix_mul_equiv _ _ e e e,
    ← Matrix.submatrix_mul_equiv _ _ e e e, Matrix.submatrix_one_equiv, hc] at hb
  change Matrix.fromBlocks (-dT) 0 A dC * splitMatrix H +
    splitMatrix H * Matrix.fromBlocks (-dT) 0 A dC = 1 at hb
  rw [← Matrix.fromBlocks_toBlocks (splitMatrix H)] at hb
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, Matrix.fromBlocks_add] at hb
  have hb' := Matrix.fromBlocks_inj.mp (hb.trans Matrix.fromBlocks_one.symm)
  simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero, Matrix.neg_mul, Matrix.mul_neg] at hb'
  refine ⟨?_, ?_, ?_⟩
  · have ht := hb'.2.1
    change -(dT * inverseBlock H) + inverseBlock H * dC = 0 at ht
    exact neg_add_eq_zero.mp ht
  · change dT * (splitMatrix H).toBlocks₁₁ + (splitMatrix H).toBlocks₁₁ * dT = _
    rw [← hb'.1]
    change _ = (splitMatrix H).toBlocks₁₂ * A -
      (-(dT * (splitMatrix H).toBlocks₁₁) + ( -((splitMatrix H).toBlocks₁₁ * dT) + (splitMatrix H).toBlocks₁₂ * A))
    abel
  · simp only [targetBlock, Matrix.neg_mul, Matrix.mul_neg]
    rw [← hb'.2.2.2]
    change _ = A * (splitMatrix H).toBlocks₁₂ -
      ((A * (splitMatrix H).toBlocks₁₂ + dC * (splitMatrix H).toBlocks₂₂) + (splitMatrix H).toBlocks₂₂ * dC)
    abel

theorem inverseBlock_homogeneous (source : Vector ℤ m) (target : Vector ℤ n)
    (H : Matrix (Fin (m+n)) (Fin (m+n)) R)
    (hH : Homogeneous (coneDegree source target) (coneDegree source target) (-1) H) :
    Homogeneous target source 0 (inverseBlock H) := by
  intro i j hij
  apply hH (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inr j))
  rw [coneDegree_get, coneDegree_get]
  simp only [Sum.elim_inl, Sum.elim_inr]
  omega

theorem sourceBlock_homogeneous (source : Vector ℤ m) (target : Vector ℤ n)
    (H : Matrix (Fin (m+n)) (Fin (m+n)) R)
    (hH : Homogeneous (coneDegree source target) (coneDegree source target) (-1) H) :
    Homogeneous source source (-1) (sourceBlock H) := by
  intro i j hij
  apply hH (finSumFinEquiv (.inl i)) (finSumFinEquiv (.inl j))
  rw [coneDegree_get, coneDegree_get]
  simp only [Sum.elim_inl]
  omega

theorem targetBlock_homogeneous (source : Vector ℤ m) (target : Vector ℤ n)
    (H : Matrix (Fin (m+n)) (Fin (m+n)) R)
    (hH : Homogeneous (coneDegree source target) (coneDegree source target) (-1) H) :
    Homogeneous target target (-1) (targetBlock H) := by
  intro i j hij
  change -H (finSumFinEquiv (.inr i)) (finSumFinEquiv (.inr j)) = 0
  rw [hH _ _ (by simpa only [coneDegree_get, Sum.elim_inr] using hij), neg_zero]

end
end Decoupling.HighDim.AlgorithmTwoFiniteComplex
