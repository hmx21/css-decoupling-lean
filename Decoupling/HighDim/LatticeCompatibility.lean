import Decoupling.HighDim.LatticeExt

/-!
# Physical and categorical Ext agree for arbitrary retained sublattices

The retained reduced module is the actual cokernel of the dagger of the
expanded physical check matrix. Its conjugated derived Ext is identified
with restriction of the original Ext, using the proved trace pairing.
-/

namespace Decoupling.HighDim.LatticeCompatibility

open LatticeRestriction LatticePhysical LatticeExt
  CategoryTheory CategoryTheory.Abelian Matrix
open scoped ModuleCat.Algebra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

variable (K : Type) [CommRing K] {D : ℕ}
variable (Λ : AddSubgroup (Translation D)) [Λ.FiniteIndex]
  {q s r : ℕ} (c : CSS.Checks K D q s r)

/-- The actual expanded X check matrix over the literal retained subring. -/
def H_X : Matrix (Fin s × Coset Λ) (Fin q × Coset Λ) (S K Λ) := expandMatrix K Λ c.H_X

/-- The actual expanded Z check matrix over the literal retained subring. -/
def H_Z : Matrix (Fin r × Coset Λ) (Fin q × Coset Λ) (S K Λ) := expandMatrix K Λ c.H_Z

/-- Both physical topological exactness equalities hold on every retained lattice. -/
theorem topological (hc : c.Topological) :
    (∀ v, H_X K Λ c *ᵥ v = 0 ↔ ∃ w, daggerS K Λ (H_Z K Λ c) *ᵥ w = v) ∧
    (∀ v, H_Z K Λ c *ᵥ v = 0 ↔ ∃ w, daggerS K Λ (H_X K Λ c) *ᵥ w = v) := by
  constructor
  · change ∀ v, expandMatrix K Λ c.H_X *ᵥ v = 0 ↔
      ∃ w, daggerS K Λ (expandMatrix K Λ c.H_Z) *ᵥ w = v
    rw [← expandMatrix_dagger]
    exact exactness_preserved K Λ _ _ (c.exact_X hc)
  · change ∀ v, expandMatrix K Λ c.H_Z *ᵥ v = 0 ↔
      ∃ w, daggerS K Λ (expandMatrix K Λ c.H_X) *ᵥ w = v
    rw [← expandMatrix_dagger]
    exact exactness_preserved K Λ _ _ (c.exact_Z hc)

def reduced : ModuleCat (S K Λ) :=
  ModuleCat.of (S K Λ) (((Fin q × Coset Λ) → S K Λ) ⧸
    LinearMap.range (daggerS K Λ (H_X K Λ c)).mulVecLin)

theorem reduced_range :
    ((LinearMap.range (dagger c.H_X).mulVecLin).restrictScalars (S K Λ)).map
        (vectorEquiv K Λ (Fin q)).toLinearMap =
      LinearMap.range (daggerS K Λ (H_X K Λ c)).mulVecLin := by
  ext v
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    refine ⟨expandVector K Λ z, ?_⟩
    change daggerS K Λ (expandMatrix K Λ c.H_X) *ᵥ expandVector K Λ z =
      expandVector K Λ (dagger c.H_X *ᵥ z)
    rw [← expandMatrix_dagger, expandMatrix_mulVec]
  · rintro ⟨z, rfl⟩
    obtain ⟨z, rfl⟩ := (vectorEquiv K Λ (Fin s)).surjective z
    refine ⟨dagger c.H_X *ᵥ z, ⟨z, rfl⟩, ?_⟩
    change expandVector K Λ (dagger c.H_X *ᵥ z) =
      daggerS K Λ (expandMatrix K Λ c.H_X) *ᵥ expandVector K Λ z
    rw [← expandMatrix_dagger, expandMatrix_mulVec]

/-- The physical reduced quotient is restriction of the original reduced module. -/
def reducedRestrictionEquiv : (restriction K Λ).obj (Layers.reduced c) ≃ₗ[S K Λ]
    ((Fin q → (Laurent K D)) ⧸ (LinearMap.range (dagger c.H_X).mulVecLin).restrictScalars (S K Λ)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def reducedEquiv : (restriction K Λ).obj (Layers.reduced c) ≃ₗ[S K Λ] reduced K Λ c :=
  (reducedRestrictionEquiv K Λ c).trans (Submodule.Quotient.equiv
    ((LinearMap.range (dagger c.H_X).mulVecLin).restrictScalars (S K Λ))
    (LinearMap.range (daggerS K Λ (H_X K Λ c)).mulVecLin)
    (vectorEquiv K Λ (Fin q)) (reduced_range K Λ c))

def reducedConjugateIso :
    (restriction K Λ).obj (Layers.conjugate (Layers.reduced c)) ≅
      conjugateS K Λ (reduced K Λ c) :=
  moduleIso ((conjugationRestrictionEquiv K Λ (Layers.reduced c)).trans
    (conjugateMapEquiv K Λ (M := (restriction K Λ).obj (Layers.reduced c))
      (N := reduced K Λ c) (reducedEquiv K Λ c)))

/-- Genuine Ext of the actual physically expanded check matrix. -/
abbrev E_X (i : ℕ) :=
  Ext (conjugateS K Λ (reduced K Λ c)) (ModuleCat.of (S K Λ) (S K Λ)) i

/-- Physical/categorical compatibility, with the current manuscript's conjugate
reduced-module convention, for every finite-index lattice and every degree. -/
def E_XEquiv (i : ℕ) : Layers.E_X c i ≃ₗ[S K Λ] E_X K Λ c i :=
  (extEquiv K Λ (Layers.conjugate (Layers.reduced c)) i).trans
    (sourceEquiv K Λ (reducedConjugateIso K Λ c) _ i)

/-- Explicit compatibility with the genuine exact-functor map on Ext:
the only endpoint operations are the proved physical quotient isomorphism
and the actual retained-coefficient trace. -/
theorem E_XEquiv_apply (i : ℕ) (e : Layers.E_X c i) :
    E_XEquiv K Λ c i e = (Ext.mk₀ (reducedConjugateIso K Λ c).inv).comp
      ((e.mapExactFunctor (restriction K Λ)).comp
        (Ext.mk₀ (traceMorphism K Λ)) (add_zero i)) (zero_add i) := by
  change (Ext.mk₀ (reducedConjugateIso K Λ c).inv).comp
    (extEquiv K Λ (Layers.conjugate (Layers.reduced c)) i e) (zero_add i) = _
  rw [extEquiv_apply]

end

end Decoupling.HighDim.LatticeCompatibility
