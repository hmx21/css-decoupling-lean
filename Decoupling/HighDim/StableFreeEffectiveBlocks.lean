import Decoupling.HighDim.StableFreeProjectiveMatrix
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Fixed free-coordinate block maps for represented Schanuel recursion

These are literal canonical block concatenations and selections. They
introduce no field arithmetic. Their actions match `StableFree.powerAdd`,
which is the coordinate convention of every finite retract product.
-/

namespace Decoupling.HighDim.StableFree.Effective

open Matrix CategoryTheory
noncomputable section
variable {R : Type*} [CommRing R] {a b c m : ℕ}

def columnBlocks (A : Matrix (Fin m) (Fin a) R) (B : Matrix (Fin m) (Fin b) R) :
    Matrix (Fin m) (Fin (a+b)) R :=
  (Matrix.fromCols A B).submatrix id finSumFinEquiv.symm

def rowBlocks (A : Matrix (Fin a) (Fin m) R) (B : Matrix (Fin b) (Fin m) R) :
    Matrix (Fin (a+b)) (Fin m) R :=
  (Matrix.fromRows A B).submatrix finSumFinEquiv.symm id

theorem powerAdd_apply_sum (x : Power R a) (y : Power R b) (i : Fin a ⊕ Fin b) :
    powerAdd a b (x,y) (finSumFinEquiv i) = Sum.elim x y i := by
  change Sum.elim x y (finSumFinEquiv.symm (finSumFinEquiv i)) = _
  rw [Equiv.symm_apply_apply]

theorem columnBlocks_mulVec (A : Matrix (Fin m) (Fin a) R) (B : Matrix (Fin m) (Fin b) R)
    (x : Power R a) (y : Power R b) :
    columnBlocks A B *ᵥ powerAdd a b (x,y) = A *ᵥ x + B *ᵥ y := by
  classical
  funext i
  change (∑ j : Fin (a+b), columnBlocks A B i j * powerAdd a b (x,y) j) = _
  rw [← (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a+b)).sum_comp]
  simp only [columnBlocks, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    powerAdd_apply_sum, Fintype.sum_sum_type, Matrix.fromCols, Sum.elim_inl, Sum.elim_inr]
  rfl

theorem rowBlocks_mulVec (A : Matrix (Fin a) (Fin m) R) (B : Matrix (Fin b) (Fin m) R)
    (x : Power R m) :
    rowBlocks A B *ᵥ x = powerAdd a b (A *ᵥ x,B *ᵥ x) := by
  funext i
  obtain ⟨j,rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ Fin (a+b)).surjective i
  rw [powerAdd_apply_sum]
  rcases j with j|j <;>
    simp only [rowBlocks, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromRows, Sum.elim_inl, Sum.elim_inr] <;> rfl

/-- Insert the first actual free block and zero in the second. -/
def includeFirst (a b : ℕ) : Matrix (Fin (a+b)) (Fin a) R := rowBlocks 1 0

theorem includeFirst_mulVec (x : Power R a) :
    includeFirst a b *ᵥ x = powerAdd a b (x,0) := by
  rw [includeFirst,rowBlocks_mulVec,Matrix.one_mulVec,Matrix.zero_mulVec]

/-- Select the first free block by copying rows. -/
def firstRows (A : Matrix (Fin (a+b)) (Fin m) R) : Matrix (Fin a) (Fin m) R :=
  A.submatrix (fun i => finSumFinEquiv (Sum.inl i)) id

theorem firstRows_mulVec (A : Matrix (Fin (a+b)) (Fin m) R) (x : Power R m) :
    firstRows (a := a) (b := b) A *ᵥ x = ((powerAdd a b).symm (A *ᵥ x)).1 := by
  obtain ⟨⟨y,z⟩,hy⟩ := (powerAdd a b).surjective (A *ᵥ x)
  apply funext
  intro i
  change (A *ᵥ x) (finSumFinEquiv (Sum.inl i)) = _
  rw [←hy,LinearEquiv.symm_apply_apply,powerAdd_apply_sum]
  rfl

/-- The coordinate projection of a product retract onto its first free term. -/
theorem product_embed_first {P F : ModuleCat R} (p : FiniteRetract P)
    (cF : F ≃ₗ[R] Power R a) (x : F × P) :
    ((powerAdd a p.size).symm
      (((FiniteRetract.ofCoordinates a cF).prod p).embed x)).1 = cF x.1 := by
  change ((powerAdd a p.size).symm (powerAdd a p.size (cF x.1,p.embed x.2))).1 = _
  rw [LinearEquiv.symm_apply_apply]

/-- Full coordinates of the actual product retract. -/
theorem product_embed {P F : ModuleCat R} (p : FiniteRetract P)
    (cF : F ≃ₗ[R] Power R a) (x : F × P) :
    ((FiniteRetract.ofCoordinates a cF).prod p).embed x =
      powerAdd a p.size (cF x.1,p.embed x.2) := rfl

end
end Decoupling.HighDim.StableFree.Effective
