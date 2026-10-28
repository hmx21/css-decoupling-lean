import Decoupling.ProjectiveFreeness
import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.Algebra.MonoidAlgebra.MapDomain
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.Data.Fin.Tuple.Basic

/-! # Variable-count coordinates for Laurent freeness induction -/

namespace Decoupling.LaurentVariables

open ProjectiveFreeness

noncomputable section

variable (K : Type*) [CommRing K]

abbrev Ring (n : ℕ) := AddMonoidAlgebra K (Fin n → ℤ)

def splitExponent (n : ℕ) : (Fin (n + 1) → ℤ) ≃+ ℤ × (Fin n → ℤ) where
  toFun a := (a 0, Fin.tail a)
  invFun a := Fin.cons a.1 a.2
  left_inv a := Fin.cons_self_tail a
  right_inv a := by simp
  map_add' _ _ := rfl

def successorEquiv (n : ℕ) : Ring K (n + 1) ≃+* LaurentPolynomial (Ring K n) :=
  (AddMonoidAlgebra.mapDomainRingEquiv K (splitExponent n)).trans
    AddMonoidAlgebra.curryRingEquiv

def zeroEquiv : Ring K 0 ≃+* K := AddMonoidAlgebra.uniqueRingEquiv (Fin 0 → ℤ)

theorem zero_criterion (K : Type*) [Field K] : IdempotentCriterion (Ring K 0) := by
  apply criterion_of_ringEquiv (zeroEquiv K).symm
  intro n E _
  infer_instance

end
end Decoupling.LaurentVariables
