import Decoupling.HighDim.AlgorithmTwoFiniteComplexBounded
import Decoupling.HighDim.AlgorithmTwoComparisonCone

/-! # Original finite total coordinates of the actual mapping cone -/
namespace Decoupling.HighDim.AlgorithmTwoFiniteComplex
open CategoryTheory Matrix
noncomputable section
variable {R : Type} [CommRing R]
variable {T C : CochainComplex (ModuleCat R) ℤ} {m n : ℕ}

def joinCoordinates : ((Fin m → R) × (Fin n → R)) ≃ₗ[R] (Fin (m+n) → R) :=
  (LinearEquiv.sumArrowLequivProdArrow (Fin m) (Fin n) R R).symm.trans
    (LinearEquiv.funCongrLeft R R finSumFinEquiv.symm)

@[simp] theorem joinCoordinates_inl (x : Fin m → R) (y : Fin n → R) (a : Fin m) :
    joinCoordinates (x,y) (finSumFinEquiv (.inl a)) = x a := by simp [joinCoordinates]

@[simp] theorem joinCoordinates_inr (x : Fin m → R) (y : Fin n → R) (b : Fin n) :
    joinCoordinates (x,y) (finSumFinEquiv (.inr b)) = y b := by simp [joinCoordinates]

@[simp] theorem joinCoordinates_symm_left (x : Fin (m+n) → R) :
    (joinCoordinates.symm x).1 = fun a => x (finSumFinEquiv (.inl a)) := rfl

@[simp] theorem joinCoordinates_symm_right (x : Fin (m+n) → R) :
    (joinCoordinates.symm x).2 = fun b => x (finSumFinEquiv (.inr b)) := rfl

def coneDegree (source : Vector ℤ m) (target : Vector ℤ n) : Vector ℤ (m+n) :=
  Vector.ofFn fun i => Sum.elim (fun a => source.get a - 1) (fun b => target.get b)
    (finSumFinEquiv.symm i)

theorem coneDegree_get (source : Vector ℤ m) (target : Vector ℤ n) (i : Fin m ⊕ Fin n) :
    (coneDegree source target).get (finSumFinEquiv i) =
      Sum.elim (fun a => source.get a - 1) (fun b => target.get b) i := by
  change (Vector.ofFn _)[(finSumFinEquiv i).val] = _
  rw [Vector.getElem_ofFn, Equiv.symm_apply_apply]

/-- The cone is ordered T[j+1] followed by C[j], exactly as mathlib's
actualConeTermIso. Source degree labels are consequently lowered by one. -/
def Coordinates.cone (f : T ⟶ C) (cT : Coordinates T m) (cC : Coordinates C n) :
    Coordinates (CochainComplex.mappingCone f) (m+n) where
  degree := coneDegree cT.degree cC.degree
  embed j := joinCoordinates.toLinearMap.comp
    (((cT.embed (j+1)).prodMap (cC.embed j)).comp
      (AlgorithmTwoComparison.actualConeTermIso f j).toLinearEquiv.toLinearMap)
  project j := (AlgorithmTwoComparison.actualConeTermIso f j).toLinearEquiv.symm.toLinearMap.comp
    (((cT.project (j+1)).prodMap (cC.project j)).comp joinCoordinates.symm.toLinearMap)
  project_embed j x := by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
      LinearMap.prodMap_apply, cT.project_embed, cC.project_embed, Prod.mk.eta]
  embed_project j x i := by
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
      LinearMap.prodMap_apply]
    obtain ⟨a | b, rfl⟩ := finSumFinEquiv.surjective i
    · rw [coneDegree_get]
      simp only [joinCoordinates_inl, joinCoordinates_symm_left, Sum.elim_inl]
      change cT.embed (j+1) (cT.project (j+1) (fun a => x (finSumFinEquiv (.inl a)))) a =
        if cT.degree.get a - 1 = j then x (finSumFinEquiv (.inl a)) else 0
      rw [cT.embed_project]
      simp only [sub_eq_iff_eq_add]
    · rw [coneDegree_get]
      simp only [joinCoordinates_inr, joinCoordinates_symm_right, Sum.elim_inr]
      exact cC.embed_project _ _ _

end
end Decoupling.HighDim.AlgorithmTwoFiniteComplex
