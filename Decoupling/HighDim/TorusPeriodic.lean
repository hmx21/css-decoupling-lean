import Decoupling.HighDim.CSS
import Decoupling.HighDim.LatticeRestriction
import Decoupling.HighDim.TorusHomology
import Mathlib.Algebra.MonoidAlgebra.Module

/-!
# Actual periodic CSS logical modules on arbitrary tori

Source: Corollary 3 and Appendix B.3. A period lattice is an arbitrary
additive subgroup of the integer translation lattice. Periodic coefficients
are the actual group algebra of its quotient; checks are obtained by mapping
each Laurent monomial to its coset. No rectangular-period assumption and no
trivial-action assumption on Ext layers is built into these definitions.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory Matrix
noncomputable section

variable {K : Type*} [Field K] {D q s r : ℕ}

abbrev PeriodRing (K : Type*) [CommRing K] {D : ℕ}
    (L : AddSubgroup (Translation D)) := AddMonoidAlgebra K ((Translation D) ⧸ L)

/-- Impose precisely the specified translations as periods. -/
def periodMap (L : AddSubgroup (Translation D)) : Laurent K D →+* PeriodRing K L :=
  AddMonoidAlgebra.mapDomainRingHom K (QuotientAddGroup.mk' L)

@[simp] theorem periodMap_monomial (L : AddSubgroup (Translation D)) (a : Translation D) :
    periodMap (K := K) L (monomial K a) =
      AddMonoidAlgebra.single ((QuotientAddGroup.mk' L) a) 1 := by
  simp [periodMap, monomial]

@[simp] theorem periodMap_period (L : AddSubgroup (Translation D)) (a : Translation D)
    (ha : a ∈ L) : periodMap (K := K) L (monomial K a) = 1 := by
  have h : (QuotientAddGroup.mk' L) a = 0 := (QuotientAddGroup.eq_zero_iff a).mpr ha
  rw [periodMap_monomial, h]
  rfl

/-- The actual X-syndrome map on the finite torus, viewed over the field. -/
def periodicX (L : AddSubgroup (Translation D)) (c : CSS.Checks K D q s r) :
    (Fin q → PeriodRing K L) →ₗ[K] (Fin s → PeriodRing K L) :=
  ((c.H_X.map (periodMap L)).mulVecLin).restrictScalars K

/-- The actual Z-stabilizer map, including the Laurent dagger before
periodicization. -/
def periodicZ (L : AddSubgroup (Translation D)) (c : CSS.Checks K D q s r) :
    (Fin r → PeriodRing K L) →ₗ[K] (Fin q → PeriodRing K L) :=
  (((dagger c.H_Z).map (periodMap L)).mulVecLin).restrictScalars K

/-- Topology implies that periodic stabilizers remain inside periodic
cycles, even though periodic exactness need not hold. -/
theorem periodic_comp_zero (L : AddSubgroup (Translation D)) (c : CSS.Checks K D q s r)
    (hc : c.Topological) : (periodicX L c).comp (periodicZ L c) = 0 := by
  apply LinearMap.ext
  intro v
  funext i
  change ((c.H_X.map (periodMap L)) *ᵥ ((dagger c.H_Z).map (periodMap L) *ᵥ v)) i = 0
  rw [Matrix.mulVec_mulVec, ← Matrix.map_mul, c.checks_commute hc]
  simp

/-- This is the physical short complex, not a count assigned to layers. -/
def periodicSc (L : AddSubgroup (Translation D)) (c : CSS.Checks K D q s r)
    (hc : c.Topological) : ShortComplex (ModuleCat K) :=
  ShortComplex.moduleCatMk (periodicZ L c) (periodicX L c) (periodic_comp_zero L c hc)

/-- Actual logical Pauli support module `ker H_X / im H_Z†`, over the field. -/
abbrev Logical (L : AddSubgroup (Translation D)) (c : CSS.Checks K D q s r)
    (hc : c.Topological) :=
  LinearMap.ker (periodicX L c) ⧸ (periodicSc L c hc).moduleCatToCycles.range

/-- The number of logical qudits on the specified finite torus. -/
def logicalQudits (L : AddSubgroup (Translation D)) (c : CSS.Checks K D q s r)
    (hc : c.Topological) : ℕ := Module.finrank K (Logical L c hc)

/-- Canonical identification with native homology of the physical window. -/
def periodicHomologyEquiv (L : AddSubgroup (Translation D)) (c : CSS.Checks K D q s r)
    (hc : c.Topological) : (periodicSc L c hc).homology ≃ₗ[K] Logical L c hc :=
  (periodicSc L c hc).moduleCatHomologyIso.toLinearEquiv

instance periodRing_finite (L : AddSubgroup (Translation D)) [L.FiniteIndex] :
    Module.Finite K (PeriodRing K L) := by
  let : Fintype ((Translation D) ⧸ L) := Fintype.ofFinite _
  exact Module.Finite.of_basis (AddMonoidAlgebra.basis ((Translation D) ⧸ L) K)

instance logical_finite (L : AddSubgroup (Translation D)) [L.FiniteIndex]
    (c : CSS.Checks K D q s r) (hc : c.Topological) :
    Module.Finite K (Logical L c hc) := by
  let : Module.Finite K (Fin q → PeriodRing K L) := Module.Finite.pi
  let : Module.Finite K (LinearMap.ker (periodicSc L c hc).g.hom) := by
    change Module.Finite K (LinearMap.ker (periodicX L c))
    infer_instance
  exact Module.Finite.quotient K (periodicSc L c hc).moduleCatToCycles.range

end
end Decoupling.HighDim.Torus
