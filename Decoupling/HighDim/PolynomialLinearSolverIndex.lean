import Decoupling.HighDim.EffectiveLinearCoordinates
import Decoupling.HighDim.FiniteLinearSolverKernel
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Computable indexing of polynomial coefficient boxes

HD012. Enumeration is the explicit base-(b+1) digit equivalence and the
explicit product-of-Fin equivalence. No field-dependent search or
choice of an enumeration occurs in any executable definition here.
-/
namespace Decoupling.HighDim.PolynomialLinearSolver
open EffectiveLinear
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def boxSize (N b : ℕ) : ℕ := (b + 1) ^ N

/-- A genuine finitely supported exponent, constructed without the
noncomputable finite-function-to-finsupp conversion. -/
def exponentOfFunction {N : ℕ} (a : Fin N → ℕ) : Fin N →₀ ℕ where
  support := Finset.univ.filter (fun i => a i ≠ 0)
  toFun := a
  mem_support_toFun := by intro i; simp

@[simp] theorem exponentOfFunction_apply {N : ℕ} (a : Fin N → ℕ) (i : Fin N) :
    exponentOfFunction a i = a i := rfl

def exponentAt (N b : ℕ) (k : Fin (boxSize N b)) : BoxExponent N b :=
  ⟨exponentOfFunction (fun i => ((finFunctionFinEquiv (m := b + 1) (n := N)).symm k i).val),
    fun i => Nat.le_of_lt_succ (((finFunctionFinEquiv (m := b + 1) (n := N)).symm k i).isLt)⟩

def exponentIndex (N b : ℕ) (a : BoxExponent N b) : Fin (boxSize N b) :=
  finFunctionFinEquiv (fun i => (⟨a.val i, Nat.lt_succ_of_le (a.property i)⟩ : Fin (b + 1)))

def boxIndex (N b : ℕ) : Fin (boxSize N b) ≃ BoxExponent N b where
  toFun := exponentAt N b
  invFun := exponentIndex N b
  left_inv k := by
    change finFunctionFinEquiv ((finFunctionFinEquiv (m := b + 1) (n := N)).symm k) = k
    exact Equiv.apply_symm_apply _ _
  right_inv a := by
    apply Subtype.ext
    apply Finsupp.ext
    intro i
    have h := congrFun ((finFunctionFinEquiv (m := b + 1) (n := N)).symm_apply_apply
      (fun i => (⟨a.val i, Nat.lt_succ_of_le (a.property i)⟩ : Fin (b + 1)))) i
    exact congrArg Fin.val h

/-- Flat dense coordinates for a vector of boxed polynomials. -/
def systemIndex (N m b : ℕ) : Fin (m * boxSize N b) ≃ Fin m × BoxExponent N b :=
  finProdFinEquiv.symm.trans (Equiv.prodCongr (Equiv.refl _) (boxIndex N b))

end Decoupling.HighDim.PolynomialLinearSolver
