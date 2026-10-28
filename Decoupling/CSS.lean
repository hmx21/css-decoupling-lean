import Decoupling.Laurent
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# CSS input conventions (main.pdf, equations (1)–(4), (10))

This file distinguishes the reduced Pauli module `M_X = coker H_X†`
from the syndrome module `N = coker H_X`. Both are actual module quotients.
The two topological equalities are explicit hypotheses, not axioms.
No Ext group is defined as a stand-in for an unproved derived-functor equality.
-/

namespace Decoupling.CSS

open Matrix

noncomputable section

variable {q s r : ℕ}

abbrev Free (n : ℕ) := Fin n → R

/-- H_X has s rows and q columns; H_Z has r rows and q columns. -/
structure Checks (q s r : ℕ) where
  H_X : Matrix (Fin s) (Fin q) R
  H_Z : Matrix (Fin r) (Fin q) R

namespace Checks

variable (c : Checks q s r)

abbrev M_X := Free q ⧸ LinearMap.range (Matrix.mulVecLin (dagger c.H_X))
abbrev N := Free s ⧸ LinearMap.range (Matrix.mulVecLin c.H_X)

/-- Assumption 1, with both sectors retained. -/
def Topological : Prop :=
  LinearMap.ker (Matrix.mulVecLin c.H_X) =
      LinearMap.range (Matrix.mulVecLin (dagger c.H_Z)) ∧
    LinearMap.ker (Matrix.mulVecLin c.H_Z) =
      LinearMap.range (Matrix.mulVecLin (dagger c.H_X))

/-- The X-sector physical exactness, in elementwise image form. -/
theorem exact_X (h : c.Topological) (v : Free q) :
    c.H_X *ᵥ v = 0 ↔ ∃ z, dagger c.H_Z *ᵥ z = v := by
  change v ∈ LinearMap.ker (Matrix.mulVecLin c.H_X) ↔
    v ∈ LinearMap.range (Matrix.mulVecLin (dagger c.H_Z))
  rw [h.1]

/-- The second topological equality is not dropped when fixing the X sector. -/
theorem exact_Z (h : c.Topological) (v : Free q) :
    c.H_Z *ᵥ v = 0 ↔ ∃ z, dagger c.H_X *ᵥ z = v := by
  change v ∈ LinearMap.ker (Matrix.mulVecLin c.H_Z) ↔
    v ∈ LinearMap.range (Matrix.mulVecLin (dagger c.H_X))
  rw [h.2]

end Checks
end
end Decoupling.CSS
