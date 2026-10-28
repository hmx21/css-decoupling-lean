import Decoupling.RetainedKoszul
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-! Direction-first repeated matrices and linear maps, including zero copies. -/

namespace Decoupling.MatrixCopies

noncomputable section

variable {A B C D : Type*} [CommRing A]
  [AddCommGroup B] [Module A B] [AddCommGroup C] [Module A C]
  [AddCommGroup D] [Module A D]
  {m k l : Type*}

/-- Repeat a map independently on t copies, retaining `(direction, copy)` order. -/
def across (t : ℕ) (f : (m → B) →ₗ[A] (k → C)) :
    ((m × Fin t) → B) →ₗ[A] ((k × Fin t) → C) :=
  LinearMap.pi fun i => (LinearMap.proj i.1).comp
    (f.comp (LinearMap.pi fun j => LinearMap.proj (j, i.2)))

@[simp] theorem across_apply (t : ℕ) (f : (m → B) →ₗ[A] (k → C))
    (a : (m × Fin t) → B) (i : k) (j : Fin t) :
    across t f a (i, j) = f (fun k => a (k, j)) i := rfl

theorem across_comp (t : ℕ) (f : (k → C) →ₗ[A] (l → D))
    (g : (m → B) →ₗ[A] (k → C)) :
    across t (f.comp g) = (across t f).comp (across t g) := rfl

theorem exact_across (t : ℕ) (f : (m → B) →ₗ[A] (k → C))
    (g : (k → C) →ₗ[A] (l → D))
    (h : LinearMap.range f = LinearMap.ker g) :
    LinearMap.range (across t f) = LinearMap.ker (across t g) := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    ext i
    change g (f (fun j => b (j, i.2))) i.1 = 0
    have hz : f (fun j => b (j, i.2)) ∈ LinearMap.ker g := by
      rw [← h]
      exact ⟨_, rfl⟩
    exact congrFun hz i.1
  · intro ha
    have each (j : Fin t) : ∃ b, f b = fun i => a (i, j) := by
      have hz : (fun i => a (i, j)) ∈ LinearMap.ker g := by
        funext i
        exact congrFun ha (i, j)
      rw [← h] at hz
      exact hz
    choose b hb using each
    refine ⟨fun i => b i.2 i.1, ?_⟩
    funext i
    exact congrFun (hb i.2) i.1

section Matrices

variable [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]

omit [Fintype k] [DecidableEq m] [DecidableEq k] in
/-- Repetition is precisely the Kronecker product with the copy identity. -/
theorem across_matrix (t : ℕ) (D : Matrix k m A) :
    across t D.mulVecLin = (Matrix.kronecker D (1 : Matrix (Fin t) (Fin t) A)).mulVecLin := by
  apply LinearMap.ext
  intro a
  funext i
  rcases i with ⟨i, j⟩
  simp [across_apply, Matrix.mulVec, dotProduct,
    Fintype.sum_prod_type, Matrix.one_apply]

end Matrices
end
end Decoupling.MatrixCopies
