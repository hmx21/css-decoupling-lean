import Decoupling.HighDim.GluedDirectionalBasis

/-!
# Actual finite matrices in the explicit directional coarse cells

Each column represents a physical species in a specified residue row.
The expansion is proved compatible with the original matrix action and
with Laurent dagger, so both stabilizer sectors retain their semantics.
-/

namespace Decoupling.HighDim.GluedDirectional

open CategoryTheory Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime]

def operatorMatrix {m n : ℕ}
    (f : restrictedFree p n →ₗ[Laurent (ZMod p) 3] restrictedFree p m) :
    Matrix (Fin m × Fin p) (Fin n × Fin p) (Laurent (ZMod p) 3) :=
  LinearMap.toMatrix' ((vectorCoordinates p m).toLinearMap.comp
    (f.comp (vectorCoordinates p n).symm.toLinearMap))

theorem operatorMatrix_mulVec {m n : ℕ}
    (f : restrictedFree p n →ₗ[Laurent (ZMod p) 3] restrictedFree p m)
    (v : (Fin n × Fin p) → Laurent (ZMod p) 3) :
    operatorMatrix p f *ᵥ v = vectorCoordinates p m (f ((vectorCoordinates p n).symm v)) :=
  LinearMap.toMatrix'_mulVec _ _

@[simp] theorem operatorMatrix_zero {m n : ℕ} :
    operatorMatrix p (0 : restrictedFree p n →ₗ[Laurent (ZMod p) 3] restrictedFree p m) = 0 := by
  simp [operatorMatrix]

@[simp] theorem operatorMatrix_id (n : ℕ) :
    operatorMatrix p (LinearMap.id : restrictedFree p n →ₗ[Laurent (ZMod p) 3] restrictedFree p n) = 1 := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp [operatorMatrix_mulVec]

@[simp] theorem operatorMatrix_add {m n : ℕ}
    (f g : restrictedFree p n →ₗ[Laurent (ZMod p) 3] restrictedFree p m) :
    operatorMatrix p (f + g) = operatorMatrix p f + operatorMatrix p g := by
  simp [operatorMatrix, LinearMap.add_comp, LinearMap.comp_add]

@[simp] theorem operatorMatrix_sub {m n : ℕ}
    (f g : restrictedFree p n →ₗ[Laurent (ZMod p) 3] restrictedFree p m) :
    operatorMatrix p (f - g) = operatorMatrix p f - operatorMatrix p g := by
  simp [operatorMatrix, LinearMap.sub_comp, LinearMap.comp_sub]

theorem operatorMatrix_comp {l m n : ℕ}
    (f : restrictedFree p m →ₗ[Laurent (ZMod p) 3] restrictedFree p l)
    (g : restrictedFree p n →ₗ[Laurent (ZMod p) 3] restrictedFree p m) :
    operatorMatrix p (f.comp g) = operatorMatrix p f * operatorMatrix p g := by
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  simp [operatorMatrix_mulVec]

def expandMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) (Laurent (ZMod p) 3)) :
    Matrix (Fin m × Fin p) (Fin n × Fin p) (Laurent (ZMod p) 3) :=
  operatorMatrix p (restrictMatrix p A)

theorem expandMatrix_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) (Laurent (ZMod p) 3))
    (v : Fin n → Laurent (ZMod p) 3) :
    expandMatrix p A *ᵥ vectorCoordinates p n v = vectorCoordinates p m (A *ᵥ v) := by
  rw [expandMatrix, operatorMatrix_mulVec, LinearEquiv.symm_apply_apply]
  rfl

theorem expandMatrix_entry {m n : ℕ} (A : Matrix (Fin m) (Fin n) (Laurent (ZMod p) 3))
    (i : Fin m) (j : Fin n) (r t : Fin p) :
    expandMatrix p A (i, r) (j, t) =
      rowCoordinates p (A i j * monomial (ZMod p) (row p t)) r := by
  rw [expandMatrix, operatorMatrix, LinearMap.toMatrix'_apply]
  change vectorCoordinates p m
    (A *ᵥ (vectorCoordinates p n).symm (Pi.single (j, t) 1)) (i, r) = _
  rw [vectorCoordinates_symm_single]
  change rowCoordinates p ((A *ᵥ Pi.single j (monomial (ZMod p) (row p t))) i) r = _
  simp [Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_ite_eq', mul_ite]

theorem expandMatrix_coeff {m n : ℕ} (A : Matrix (Fin m) (Fin n) (Laurent (ZMod p) 3))
    (i : Fin m) (j : Fin n) (r t : Fin p) (a : Translation 3) :
    (expandMatrix p A (i, r) (j, t)).coeff a =
      (A i j).coeff (inclusion p a + row p r - row p t) := by
  rw [expandMatrix_entry, rowCoordinates_coeff]
  simp [monomial, sub_eq_add_neg]

theorem expandMatrix_dagger {m n : ℕ} (A : Matrix (Fin m) (Fin n) (Laurent (ZMod p) 3)) :
    expandMatrix p (dagger A) = dagger (expandMatrix p A) := by
  apply Matrix.ext
  rintro ⟨i, r⟩ ⟨j, t⟩
  apply AddMonoidAlgebra.coeff_injective
  apply Finsupp.ext
  intro a
  change (expandMatrix p (dagger A) (i, r) (j, t)).coeff a =
    (bar (expandMatrix p A (j, t) (i, r))).coeff a
  rw [expandMatrix_coeff, bar_coeff, expandMatrix_coeff]
  change (bar (A j i)).coeff _ = _
  rw [bar_coeff, (inclusion p).map_neg]
  congr 1
  abel

theorem expandMatrix_exact {l m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (Laurent (ZMod p) 3))
    (B : Matrix (Fin n) (Fin l) (Laurent (ZMod p) 3))
    (h : ∀ v, A *ᵥ v = 0 ↔ ∃ z, B *ᵥ z = v)
    (v : (Fin n × Fin p) → Laurent (ZMod p) 3) :
    expandMatrix p A *ᵥ v = 0 ↔ ∃ z, expandMatrix p B *ᵥ z = v := by
  obtain ⟨v, rfl⟩ := (vectorCoordinates p n).surjective v
  rw [expandMatrix_mulVec, (vectorCoordinates p m).map_eq_zero_iff, h]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨vectorCoordinates p l z, expandMatrix_mulVec p B z⟩
  · rintro ⟨z, hz⟩
    obtain ⟨z, rfl⟩ := (vectorCoordinates p l).surjective z
    rw [expandMatrix_mulVec] at hz
    exact ⟨z, (vectorCoordinates p n).injective hz⟩

end
end Decoupling.HighDim.GluedDirectional
