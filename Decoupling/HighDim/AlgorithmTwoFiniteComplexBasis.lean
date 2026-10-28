import Decoupling.HighDim.AlgorithmTwoFiniteComplexMatrix

/-! # Construction of total coordinates from the actual degreewise bases -/
namespace Decoupling.HighDim.AlgorithmTwoFiniteComplex
open CategoryTheory Matrix
noncomputable section
universe u
variable {R : Type u} [CommRing R]
variable {C : CochainComplex (ModuleCat R) ℤ} {n : ℕ}

abbrev Fiber (degree : Vector ℤ n) (j : ℤ) := {i : Fin n // degree.get i = j}

def fiberEmbed (degree : Vector ℤ n) (j : ℤ) : (Fiber degree j → R) →ₗ[R] (Fin n → R) where
  toFun x i := if hi : degree.get i = j then x ⟨i,hi⟩ else 0
  map_add' x y := by funext i; simp only [Pi.add_apply]; split_ifs <;> simp_all
  map_smul' a x := by funext i; simp only [Pi.smul_apply]; split_ifs <;> simp_all

def fiberProject (degree : Vector ℤ n) (j : ℤ) : (Fin n → R) →ₗ[R] (Fiber degree j → R) where
  toFun x i := x i.val
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem fiberProject_embed (degree : Vector ℤ n) (j : ℤ) (x : Fiber degree j → R) :
    fiberProject degree j (fiberEmbed degree j x) = x := by
  funext i
  simp [fiberProject, fiberEmbed, i.property]

/-- Relabelling the original free basis by its finite total index does not
introduce a new freeness or splitting hypothesis. -/
def Coordinates.ofDegreewise (degree : Vector ℤ n)
    (e : ∀ j, C.X j ≃ₗ[R] (Fiber degree j → R)) : Coordinates C n where
  degree := degree
  embed j := (fiberEmbed degree j).comp (e j).toLinearMap
  project j := (e j).symm.toLinearMap.comp (fiberProject degree j)
  project_embed j x := by simp
  embed_project j x i := by
    change fiberEmbed degree j (e j ((e j).symm (fiberProject degree j x))) i = _
    rw [LinearEquiv.apply_symm_apply]
    simp only [fiberEmbed, fiberProject, LinearMap.coe_mk, AddHom.coe_mk]
    split_ifs <;> rfl

end
end Decoupling.HighDim.AlgorithmTwoFiniteComplex
