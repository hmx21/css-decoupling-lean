import Decoupling.HighDim.ToricHodgeDifferential

/-!
# Diagonal cell translations and the conjugate Koszul differential

Changing each directional weight by a unit induces the explicitly
constructed exterior diagonal change of the actual ordered cell basis.
The Laurent specialization identifies the antipode-conjugated boundary
with the original boundary, with all minus signs retained.
-/

namespace Decoupling.HighDim.Toric.Hodge

open Koszul

noncomputable section
variable (A : Type*) [CommRing A] {D k : ℕ}

def cellUnit (u : Fin D → Aˣ) (I : Cell D k) : Aˣ := ∏ i : Fin k, u (I i)

def gauge (u : Fin D → Aˣ) (k : ℕ) : Term A D k ≃ₗ[A] Term A D k :=
  (Finsupp.linearEquivFunOnFinite A A (Cell D k)).trans
    ((LinearEquiv.piCongrRight (fun I => LinearEquiv.smulOfUnit (cellUnit A u I))).trans
      (Finsupp.linearEquivFunOnFinite A A (Cell D k)).symm)

@[simp] theorem gauge_apply (u : Fin D → Aˣ) (x : Term A D k) (I : Cell D k) :
    gauge A u k x I = (cellUnit A u I : A) * x I := rfl

theorem gauge_single (u : Fin D → Aˣ) (I : Cell D k) (a : A) :
    gauge A u k (Finsupp.single I a) = Finsupp.single I ((cellUnit A u I : A) * a) := by
  classical
  ext J
  by_cases h : I = J
  · subst J; simp
  · simp [h]

theorem cellUnit_face (u : Fin D → Aˣ) (I : Cell D (k + 1)) (i : Fin (k + 1)) :
    cellUnit A u I = u (I i) * cellUnit A u (face I i) := by
  simpa only [cellUnit, face, Function.comp_apply, RelEmbedding.coe_trans, Fin.succAboveOrderEmb_apply] using
    Fin.prod_univ_succAbove (fun a => u (I a)) i

theorem gauge_boundary (u : Fin D → Aˣ) (w w' : Fin D → A)
    (h : ∀ i, w' i * (u i : A) = w i) (k : ℕ) :
    (boundary A w' k).hom.comp (gauge A u (k + 1)).toLinearMap =
      (gauge A u k).toLinearMap.comp (boundary A w k).hom := by
  apply (Finsupp.basisSingleOne : Module.Basis (Cell D (k + 1)) A (Term A D (k + 1))).ext
  intro I
  change boundary A w' k (gauge A u (k + 1) (Finsupp.single I 1)) =
    gauge A u k (boundary A w k (Finsupp.single I 1))
  rw [gauge_single, mul_one]
  have hs : Finsupp.single I (cellUnit A u I : A) =
      (cellUnit A u I : A) • Finsupp.single I 1 := by simp
  rw [hs, map_smul, boundary_basis, boundary_basis, map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [gauge_single, Finsupp.smul_single]
  congr 1
  rw [cellUnit_face, Units.val_mul]
  change (u (I i) : A) * (cellUnit A u (face I i) : A) *
      ((-1 : A) ^ i.val * w' (I i)) = _
  calc
    _ = (cellUnit A u (face I i) : A) * ((-1 : A) ^ i.val *
        (w' (I i) * (u (I i) : A))) := by ring
    _ = _ := by rw [h]

variable (K : Type*) [CommRing K]

def directionUnit (i : Fin D) : (Laurent K D)ˣ :=
  ⟨-coordinate K i, -monomial K (-translationBasis i), by simp [coordinate],
    by simp [coordinate]⟩

theorem bar_difference_unit (i : Fin D) :
    bar (difference K i) * (directionUnit K i : Laurent K D) = difference K i := by
  change bar (coordinate K i - 1) * (-coordinate K i) = coordinate K i - 1
  simp only [bar_sub, bar_one, coordinate, bar_monomial]
  rw [sub_mul, mul_neg, monomial_neg_mul]
  ring

def laurentGauge (k : ℕ) :
    Term (Laurent K D) D k ≃ₗ[Laurent K D] Term (Laurent K D) D k :=
  gauge (Laurent K D) (directionUnit K) k

theorem laurentGauge_boundary (k : ℕ) :
    (boundary (Laurent K D) (fun i => bar (difference K i)) k).hom.comp
        (laurentGauge K k.succ).toLinearMap =
      (laurentGauge K k).toLinearMap.comp (boundary (Laurent K D) (difference K) k).hom :=
  gauge_boundary (Laurent K D) (directionUnit K) (difference K)
    (fun i => bar (difference K i)) (bar_difference_unit K) k

end
end Decoupling.HighDim.Toric.Hodge
