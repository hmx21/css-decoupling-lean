import Decoupling.HighDim.CohomologyPresentation
import Mathlib.Data.Matrix.Block

/-!
# HD012 relations for actual cohomology generators

The matrix `[W | -b]` is formed from the actual cycle generators and incoming
differential. Projecting its kernel generators gives exactly the relations
among the classes of W. This supplies the relation contract used by
`CohomologyPresentation.cohomologyEquiv`; it does not assume a presentation
of cohomology as extra data about the code.
-/
namespace Decoupling.HighDim.CohomologyPresentation
open Matrix
noncomputable section

variable {K : Type} [Field K] {D m q g t : ℕ}
  (b : Matrix (Fin q) (Fin m) (Laurent K D))
  (W : Matrix (Fin q) (Fin g) (Laurent K D))

def relationSystem : Matrix (Fin q) (Fin g ⊕ Fin m) (Laurent K D) :=
  Matrix.fromCols W (-b)

theorem relationSystem_mulVec (z : (Fin g ⊕ Fin m) → Laurent K D) :
    relationSystem b W *ᵥ z =
      W *ᵥ (fun j => z (Sum.inl j)) - b *ᵥ (fun j => z (Sum.inr j)) := by
  classical
  ext i
  simp [relationSystem, Matrix.mulVec, dotProduct, Fintype.sum_sum_type,
    Finset.sum_neg_distrib, sub_eq_add_neg]

def relationProjection (V : Matrix (Fin g ⊕ Fin m) (Fin t) (Laurent K D)) :
    Matrix (Fin g) (Fin t) (Laurent K D) := V.submatrix Sum.inl id

theorem relationProjection_mulVec
    (V : Matrix (Fin g ⊕ Fin m) (Fin t) (Laurent K D)) (u : Fin t → Laurent K D) :
    relationProjection V *ᵥ u = fun i => (V *ᵥ u) (Sum.inl i) := rfl

/-- The output of a genuine kernel routine on `[W | -b]` supplies all and
only the relations of the actual cohomology generators. -/
theorem relationProjection_range
    (V : Matrix (Fin g ⊕ Fin m) (Fin t) (Laurent K D))
    (hV : V.mulVecLin.range = (relationSystem b W).mulVecLin.ker) :
    (relationProjection V).mulVecLin.range = relations b W := by
  ext y
  constructor
  · rintro ⟨u, rfl⟩
    have hz : V *ᵥ u ∈ (relationSystem b W).mulVecLin.ker := by
      rw [← hV]
      exact ⟨u, rfl⟩
    change relationSystem b W *ᵥ (V *ᵥ u) = 0 at hz
    rw [relationSystem_mulVec, sub_eq_zero] at hz
    change ∃ z, b *ᵥ z = W *ᵥ (relationProjection V *ᵥ u)
    exact ⟨fun j => (V *ᵥ u) (Sum.inr j), hz.symm⟩
  · rintro ⟨z, hz⟩
    let x : (Fin g ⊕ Fin m) → Laurent K D := Sum.elim y z
    have hx : x ∈ (relationSystem b W).mulVecLin.ker := by
      change relationSystem b W *ᵥ x = 0
      rw [relationSystem_mulVec]
      change W *ᵥ y - b *ᵥ z = 0
      exact sub_eq_zero.mpr hz.symm
    rw [← hV] at hx
    obtain ⟨u, hu⟩ := hx
    refine ⟨u, ?_⟩
    funext i
    exact congrFun hu (Sum.inl i)

end
end Decoupling.HighDim.CohomologyPresentation
