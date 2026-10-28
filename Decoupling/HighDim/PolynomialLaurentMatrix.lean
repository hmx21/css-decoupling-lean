import Decoupling.HighDim.PolynomialLaurentExactness

/-!
# HD014 clearing the actual generators without changing their Laurent image

A finite Laurent generator matrix is shifted by a common unit. Its
polynomial lift has exactly the original Laurent column image after
localization. In particular this constructs the polynomial submodule
whose resolution is used in A2, rather than postulating one.
-/
namespace Decoupling.HighDim.PolynomialLaurent
open Matrix
noncomputable section
variable {K : Type*} [CommRing K] {D m n : ℕ}
set_option backward.isDefEq.respectTransparency false

theorem range_shift (A : Matrix (Fin m) (Fin n) (Laurent K D)) (a : Translation D) :
    LinearMap.range (monomial K a • A).mulVecLin = LinearMap.range A.mulVecLin := by
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    refine ⟨monomial K a • y,?_⟩
    change A*ᵥ(monomial K a • y) = (monomial K a • A)*ᵥy
    rw [Matrix.mulVec_smul,Matrix.smul_mulVec]
  · rintro ⟨y,rfl⟩
    refine ⟨monomial K (-a) • y,?_⟩
    change (monomial K a • A)*ᵥ(monomial K (-a) • y) = A*ᵥy
    rw [Matrix.smul_mulVec,Matrix.mulVec_smul,smul_smul,monomial_mul_neg,one_smul]

theorem exists_cleared_matrix (A : Matrix (Fin m) (Fin n) (Laurent K D)) :
    ∃ h : ℕ, ∃ B : Matrix (Fin m) (Fin n) (Poly D K),
      B.map (inclusion D K) = monomial K (constantExponent D h) • A ∧
        LinearMap.range (B.map (inclusion D K)).mulVecLin = LinearMap.range A.mulVecLin := by
  obtain ⟨h,g,hg⟩ := finite_family_clear (fun z : Fin m × Fin n => A z.1 z.2)
  let B : Matrix (Fin m) (Fin n) (Poly D K) := fun i j => g (i,j)
  have he : B.map (inclusion D K) = monomial K (constantExponent D h) • A := by
    funext i j
    exact hg (i,j)
  refine ⟨h,B,he,?_⟩
  rw [he]
  exact range_shift A _

/-- A genuine polynomial presentation of the original Laurent column image. -/
structure ClearedMatrix (A : Matrix (Fin m) (Fin n) (Laurent K D)) where
  radius : ℕ
  matrix : Matrix (Fin m) (Fin n) (Poly D K)
  image_eq : matrix.map (inclusion D K) = monomial K (constantExponent D radius) • A

theorem clearedMatrix_exists (A : Matrix (Fin m) (Fin n) (Laurent K D)) : Nonempty (ClearedMatrix A) := by
  obtain ⟨h,B,he,_⟩ := exists_cleared_matrix A
  exact ⟨⟨h,B,he⟩⟩

theorem ClearedMatrix.range_eq {A : Matrix (Fin m) (Fin n) (Laurent K D)} (B : ClearedMatrix A) :
    LinearMap.range (B.matrix.map (inclusion D K)).mulVecLin = LinearMap.range A.mulVecLin := by
  rw [B.image_eq]
  exact range_shift A _

end
end Decoupling.HighDim.PolynomialLaurent
