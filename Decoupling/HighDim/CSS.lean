import Decoupling.HighDim.Laurent
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The two actual topological equalities in arbitrary D and characteristic

Source: `drafts/main.tex` 185–227 and 452–456. Check matrices are finite,
their entries are finitely supported Laurent polynomials, and their columns
are the inputs. Reduced Pauli and check-syndrome quotients are distinguished.
-/

namespace Decoupling.HighDim.CSS

open Matrix
noncomputable section

variable {K : Type*} [CommRing K] {D q s r : ℕ}

abbrev Free (K : Type*) [CommRing K] (D n : ℕ) := Fin n → Laurent K D

structure Checks (K : Type*) [CommRing K] (D q s r : ℕ) where
  H_X : Matrix (Fin s) (Fin q) (Laurent K D)
  H_Z : Matrix (Fin r) (Fin q) (Laurent K D)

namespace Checks

variable (c : Checks K D q s r)

abbrev M_X := Free K D q ⧸ LinearMap.range (dagger c.H_X).mulVecLin
abbrev M_Z := Free K D q ⧸ LinearMap.range (dagger c.H_Z).mulVecLin
abbrev CheckCokernel := Free K D s ⧸ LinearMap.range c.H_X.mulVecLin

def Topological : Prop :=
  LinearMap.ker c.H_X.mulVecLin = LinearMap.range (dagger c.H_Z).mulVecLin ∧
  LinearMap.ker c.H_Z.mulVecLin = LinearMap.range (dagger c.H_X).mulVecLin

theorem exact_X (h : c.Topological) (v : Free K D q) :
    c.H_X *ᵥ v = 0 ↔ ∃ z, dagger c.H_Z *ᵥ z = v := by
  change v ∈ LinearMap.ker c.H_X.mulVecLin ↔
    v ∈ LinearMap.range (dagger c.H_Z).mulVecLin
  rw [h.1]

theorem exact_Z (h : c.Topological) (v : Free K D q) :
    c.H_Z *ᵥ v = 0 ↔ ∃ z, dagger c.H_X *ᵥ z = v := by
  change v ∈ LinearMap.ker c.H_Z.mulVecLin ↔
    v ∈ LinearMap.range (dagger c.H_X).mulVecLin
  rw [h.2]

/-- Commutation follows from exactness; it is not substituted for exactness. -/
theorem checks_commute (h : c.Topological) : c.H_X * dagger c.H_Z = 0 := by
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec, Matrix.zero_mulVec]
  exact (c.exact_X h _).mpr ⟨v, rfl⟩

/-- Algebraic exchange of the sectors. The physical Fourier realization is
a separate obligation, not asserted by this definition. -/
def swap : Checks K D q r s := ⟨c.H_Z, c.H_X⟩

@[simp] theorem swap_swap : c.swap.swap = c := by cases c; rfl

theorem topological_swap (h : c.Topological) : c.swap.Topological := ⟨h.2, h.1⟩

/-- The actual reduced module embeds in a finite free module, by the second
topological equality. This will drive the Ext degree bound. -/
def reducedEquivRange (h : c.Topological) :
    c.M_X ≃ₗ[Laurent K D] LinearMap.range c.H_Z.mulVecLin :=
  (Submodule.quotEquivOfEq _ _ h.2.symm).trans c.H_Z.mulVecLin.quotKerEquivRange

def reducedEmbedding (h : c.Topological) : c.M_X →ₗ[Laurent K D] Free K D r :=
  (LinearMap.range c.H_Z.mulVecLin).subtype.comp (c.reducedEquivRange h).toLinearMap

theorem reducedEmbedding_injective (h : c.Topological) :
    Function.Injective (c.reducedEmbedding h) :=
  (LinearMap.range c.H_Z.mulVecLin).injective_subtype.comp (c.reducedEquivRange h).injective

@[simp] theorem reducedEmbedding_mk (h : c.Topological) (v : Free K D q) :
    c.reducedEmbedding h (Submodule.Quotient.mk v) = c.H_Z *ᵥ v := rfl

end Checks
end
end Decoupling.HighDim.CSS
