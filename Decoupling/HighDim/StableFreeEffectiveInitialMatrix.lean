import Decoupling.HighDim.StableFreeEffectiveInitialAlgebra
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! # HD012 explicit finite matrices of the first Schanuel lifting square -/
namespace Decoupling.HighDim.StableFree.Effective.Initial
open Matrix CategoryTheory
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R]

def joinCols {a b c : ℕ} (A : Matrix (Fin a) (Fin b) R) (B : Matrix (Fin a) (Fin c) R) :
    Matrix (Fin a) (Fin (b+c)) R := (Matrix.fromCols A B).submatrix id finSumFinEquiv.symm

def joinRows {a b c : ℕ} (A : Matrix (Fin a) (Fin c) R) (B : Matrix (Fin b) (Fin c) R) :
    Matrix (Fin (a+b)) (Fin c) R := (Matrix.fromRows A B).submatrix finSumFinEquiv.symm id

theorem joinCols_mulVec {a b c : ℕ} (A : Matrix (Fin a) (Fin b) R)
    (B : Matrix (Fin a) (Fin c) R) (x : Power R (b+c)) :
    joinCols A B *ᵥ x = A *ᵥ ((powerAdd b c).symm x).1 + B *ᵥ ((powerAdd b c).symm x).2 := by
  rw [joinCols, Matrix.submatrix_mulVec_equiv]
  funext i
  simp [Matrix.mulVec, dotProduct, powerAdd]

theorem joinRows_mulVec {a b c : ℕ} (A : Matrix (Fin a) (Fin c) R)
    (B : Matrix (Fin b) (Fin c) R) (x : Power R c) :
    joinRows A B *ᵥ x = powerAdd a b (A *ᵥ x, B *ᵥ x) := by
  funext i
  obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a+b)).surjective i
  cases j <;> simp [joinRows, Matrix.mulVec, dotProduct, powerAdd]

namespace Data
variable {M N : ModuleCat.{u} R} {c n p e rel : ℕ} (a : Data M N c n p e rel)

def matrixF := LinearMap.toMatrix' a.F
def matrixG := LinearMap.toMatrix' a.G
def matrixX := LinearMap.toMatrix' a.X
def matrixY := LinearMap.toMatrix' a.Y
def matrixZ := LinearMap.toMatrix' a.Z
def matrixT := LinearMap.toMatrix' a.T

def matrixL := joinCols a.matrixT (-(a.matrixF * a.matrixZ))
def matrixR := a.matrixG * a.matrixL + joinCols 0 a.matrixZ
def matrixQN := a.matrixL - a.matrixF * a.matrixR
def matrixQP := joinCols 0 (1 : Matrix (Fin p) (Fin p) R) - a.matrixX * a.matrixR
def matrixQ := joinRows (a.matrixY * a.matrixQN) a.matrixQP
def matrixBeta := joinRows (joinCols a.matrixF a.matrixQN) (joinCols a.matrixX a.matrixQP)
def matrixRelations := joinRows a.relations (0 : Matrix (Fin p) (Fin rel) R)
def matrixRightProjector :=
  joinRows (joinCols (1 : Matrix (Fin c) (Fin c) R) (0 : Matrix (Fin c) (Fin (e+p)) R))
    (joinCols (0 : Matrix (Fin (e+p)) (Fin c) R) a.matrixQ)

theorem matrixL_apply (x : Power R (e+p)) :
    a.matrixL *ᵥ x = a.leftLift ((powerAdd e p).symm x) := by
  rw [matrixL, joinCols_mulVec, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec]
  simp only [matrixT, matrixF, matrixZ, LinearMap.toMatrix'_mulVec]
  change _ = a.T ((powerAdd e p).symm x).1 - a.F (a.Z ((powerAdd e p).symm x).2)
  rw [sub_eq_add_neg]

theorem matrixR_apply (x : Power R (e+p)) :
    a.matrixR *ᵥ x = a.rightLift ((powerAdd e p).symm x) := by
  rw [matrixR, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, matrixL_apply,
    joinCols_mulVec, Matrix.zero_mulVec, zero_add]
  simp only [matrixG, matrixZ, LinearMap.toMatrix'_mulVec]
  rfl

theorem matrixQN_apply (x : Power R (e+p)) :
    a.matrixQN *ᵥ x = a.complementN ((powerAdd e p).symm x) := by
  rw [matrixQN, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, matrixL_apply, matrixR_apply]
  simp only [matrixF, LinearMap.toMatrix'_mulVec]
  rfl

theorem matrixQP_apply (x : Power R (e+p)) :
    a.matrixQP *ᵥ x = a.complementP ((powerAdd e p).symm x) := by
  rw [matrixQP, Matrix.sub_mulVec, joinCols_mulVec, Matrix.zero_mulVec,
    Matrix.one_mulVec, zero_add, ← Matrix.mulVec_mulVec, matrixR_apply]
  simp only [matrixX, LinearMap.toMatrix'_mulVec]
  rfl

theorem matrixBeta_apply (x : Power R (c+(e+p))) :
    a.matrixBeta *ᵥ x = a.betaLift x := by
  rw [matrixBeta, joinRows_mulVec, joinCols_mulVec, joinCols_mulVec,
    matrixQN_apply, matrixQP_apply]
  simp only [matrixF, matrixX, LinearMap.toMatrix'_mulVec]
  rfl

theorem betaArrow_matrix : a.betaArrow.matrix = a.matrixBeta := by
  apply Matrix.mulVec_injective
  funext x
  change LinearMap.toMatrix' a.betaLift *ᵥ x = _
  rw [LinearMap.toMatrix'_mulVec, matrixBeta_apply]

theorem matrixQ_apply (x : Power R (e+p)) :
    a.matrixQ *ᵥ x = a.complement.embed (a.complement.project x) := by
  rw [matrixQ, joinRows_mulVec, ← Matrix.mulVec_mulVec, matrixQN_apply, matrixQP_apply]
  simp only [matrixY, LinearMap.toMatrix'_mulVec]
  rw [a.Y_apply]
  change powerAdd e p
    (a.xiN (a.piN (a.complementN ((powerAdd e p).symm x))),
      a.complementP ((powerAdd e p).symm x)) =
    powerAdd e p
      (a.xiN (StableCokernel.complementRetraction a.f a.g a.xiM a.zetaM a.zetaN a.errorM
        ((powerAdd e p).symm x)).val.1,
       (StableCokernel.complementRetraction a.f a.g a.xiM a.zetaM a.zetaN a.errorM
        ((powerAdd e p).symm x)).val.2)
  rw [a.complementRetraction_projects]

theorem complement_projector : a.complement.projector = a.matrixQ := by
  apply Matrix.mulVec_injective
  funext x
  rw [FiniteRetract.projector_mulVec, matrixQ_apply]

theorem target_relations : a.target.relationMatrix = a.matrixRelations := by
  apply Matrix.mulVec_injective
  funext x
  change LinearMap.toMatrix' _ *ᵥ x = _
  rw [LinearMap.toMatrix'_mulVec, matrixRelations, joinRows_mulVec, Matrix.zero_mulVec]
  rfl

theorem sourceLeft_projector : a.sourceLeft.projector = 1 := by
  apply Matrix.mulVec_injective
  funext x
  rw [FiniteRetract.projector_mulVec, Matrix.one_mulVec]
  change powerAdd n p ((powerAdd n p).symm x) = x
  exact LinearEquiv.apply_symm_apply _ x

theorem sourceRight_projector : a.sourceRight.projector = a.matrixRightProjector := by
  apply Matrix.mulVec_injective
  funext x
  rw [FiniteRetract.projector_mulVec, matrixRightProjector, joinRows_mulVec,
    joinCols_mulVec, joinCols_mulVec, Matrix.one_mulVec, Matrix.zero_mulVec,
    Matrix.zero_mulVec, add_zero, zero_add, matrixQ_apply]
  rfl

theorem alphaArrow_matrix : a.alphaArrow.matrix = (1 : Matrix (Fin (n+p)) (Fin (n+p)) R) := by
  apply Matrix.mulVec_injective
  funext x
  change LinearMap.toMatrix' (LinearMap.id : Power R (n+p) →ₗ[R] Power R (n+p)) *ᵥ x = _
  rw [LinearMap.toMatrix'_mulVec, Matrix.one_mulVec, LinearMap.id_apply]

end Data
end
end Decoupling.HighDim.StableFree.Effective.Initial
