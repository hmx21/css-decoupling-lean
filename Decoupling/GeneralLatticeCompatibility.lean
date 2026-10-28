import Decoupling.GeneralLatticeExt

/-!
# Physical and categorical Ext agree for arbitrary retained sublattices

The retained reduced module is the actual cokernel of the dagger of the
expanded physical check matrix. Its conjugated derived Ext is identified
with restriction of the original Ext, using the proved trace pairing.
-/

namespace Decoupling.GeneralLatticeCompatibility

open GeneralLatticeRestriction GeneralLatticePhysical GeneralLatticeExt
  CategoryTheory CategoryTheory.Abelian Matrix
open scoped ModuleCat.Algebra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable (Λ : AddSubgroup Translation) [Λ.FiniteIndex]
  {q s r : ℕ} (c : CSS.Checks q s r)

/-- The actual expanded X check matrix over the literal retained subring. -/
def H_X : Matrix (Fin s × Coset Λ) (Fin q × Coset Λ) (S Λ) := expandMatrix Λ c.H_X

/-- The actual expanded Z check matrix over the literal retained subring. -/
def H_Z : Matrix (Fin r × Coset Λ) (Fin q × Coset Λ) (S Λ) := expandMatrix Λ c.H_Z

/-- Both physical topological exactness equalities hold on every retained lattice. -/
theorem topological (hc : c.Topological) :
    (∀ v, H_X Λ c *ᵥ v = 0 ↔ ∃ w, daggerS Λ (H_Z Λ c) *ᵥ w = v) ∧
    (∀ v, H_Z Λ c *ᵥ v = 0 ↔ ∃ w, daggerS Λ (H_X Λ c) *ᵥ w = v) := by
  constructor
  · change ∀ v, expandMatrix Λ c.H_X *ᵥ v = 0 ↔
      ∃ w, daggerS Λ (expandMatrix Λ c.H_Z) *ᵥ w = v
    rw [← expandMatrix_dagger]
    exact exactness_preserved Λ _ _ (c.exact_X hc)
  · change ∀ v, expandMatrix Λ c.H_Z *ᵥ v = 0 ↔
      ∃ w, daggerS Λ (expandMatrix Λ c.H_X) *ᵥ w = v
    rw [← expandMatrix_dagger]
    exact exactness_preserved Λ _ _ (c.exact_Z hc)

def reduced : ModuleCat (S Λ) :=
  ModuleCat.of (S Λ) (((Fin q × Coset Λ) → S Λ) ⧸
    LinearMap.range (daggerS Λ (H_X Λ c)).mulVecLin)

theorem reduced_range :
    ((LinearMap.range (dagger c.H_X).mulVecLin).restrictScalars (S Λ)).map
        (vectorEquiv Λ (Fin q)).toLinearMap =
      LinearMap.range (daggerS Λ (H_X Λ c)).mulVecLin := by
  ext v
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    refine ⟨expandVector Λ z, ?_⟩
    change daggerS Λ (expandMatrix Λ c.H_X) *ᵥ expandVector Λ z =
      expandVector Λ (dagger c.H_X *ᵥ z)
    rw [← expandMatrix_dagger, expandMatrix_mulVec]
  · rintro ⟨z, rfl⟩
    obtain ⟨z, rfl⟩ := (vectorEquiv Λ (Fin s)).surjective z
    refine ⟨dagger c.H_X *ᵥ z, ⟨z, rfl⟩, ?_⟩
    change expandVector Λ (dagger c.H_X *ᵥ z) =
      daggerS Λ (expandMatrix Λ c.H_X) *ᵥ expandVector Λ z
    rw [← expandMatrix_dagger, expandMatrix_mulVec]

/-- The physical reduced quotient is restriction of the original reduced module. -/
def reducedRestrictionEquiv : (restriction Λ).obj (ExtLayers.reduced c) ≃ₗ[S Λ]
    ((Fin q → R) ⧸ (LinearMap.range (dagger c.H_X).mulVecLin).restrictScalars (S Λ)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def reducedEquiv : (restriction Λ).obj (ExtLayers.reduced c) ≃ₗ[S Λ] reduced Λ c :=
  (reducedRestrictionEquiv Λ c).trans (Submodule.Quotient.equiv
    ((LinearMap.range (dagger c.H_X).mulVecLin).restrictScalars (S Λ))
    (LinearMap.range (daggerS Λ (H_X Λ c)).mulVecLin)
    (vectorEquiv Λ (Fin q)) (reduced_range Λ c))

def reducedConjugateIso :
    (restriction Λ).obj (ExtLayers.conjugate (ExtLayers.reduced c)) ≅
      conjugateS Λ (reduced Λ c) :=
  moduleIso ((conjugationRestrictionEquiv Λ (ExtLayers.reduced c)).trans
    (conjugateMapEquiv Λ (M := (restriction Λ).obj (ExtLayers.reduced c))
      (N := reduced Λ c) (reducedEquiv Λ c)))

/-- Genuine Ext of the actual physically expanded check matrix. -/
abbrev E_X (i : ℕ) :=
  Ext (conjugateS Λ (reduced Λ c)) (ModuleCat.of (S Λ) (S Λ)) i

/-- Physical/categorical compatibility, with the manuscript's conjugate
reduced-module convention, for every finite-index lattice and every degree. -/
def E_XEquiv (i : ℕ) : ExtLayers.E_X c i ≃ₗ[S Λ] E_X Λ c i :=
  (extEquiv Λ (ExtLayers.conjugate (ExtLayers.reduced c)) i).trans
    (sourceEquiv Λ (reducedConjugateIso Λ c) _ i)

/-- Explicit compatibility with the genuine exact-functor map on Ext:
the only endpoint operations are the proved physical quotient isomorphism
and the actual retained-coefficient trace. -/
theorem E_XEquiv_apply (i : ℕ) (e : ExtLayers.E_X c i) :
    E_XEquiv Λ c i e = (Ext.mk₀ (reducedConjugateIso Λ c).inv).comp
      ((e.mapExactFunctor (restriction Λ)).comp
        (Ext.mk₀ (traceMorphism Λ)) (add_zero i)) (zero_add i) := by
  change (Ext.mk₀ (reducedConjugateIso Λ c).inv).comp
    (extEquiv Λ (ExtLayers.conjugate (ExtLayers.reduced c)) i e) (zero_add i) = _
  rw [extEquiv_apply]

end

end Decoupling.GeneralLatticeCompatibility
