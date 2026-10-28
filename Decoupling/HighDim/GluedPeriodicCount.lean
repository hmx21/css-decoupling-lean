import Decoupling.HighDim.GluedRestrictedTriangle
import Decoupling.HighDim.GluedRectangular
import Decoupling.HighDim.MinimalLatticeRestriction
import Decoupling.HighDim.GluedTopology

/-!
# The actual finite-torus six-versus-four logical-qudit count

The left-hand side is the literal periodic CSS check kernel/image quotient.
It is identified with the representable functor on the actual restricted
cone triangle, where both adjacent rank losses have been computed.
-/

namespace Decoupling.HighDim.Glued

open CategoryTheory Koszul KoszulLattice Torus MinimalLattice ScalingLattice
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

variable (L : AddSubgroup (Translation 3)) [L.FiniteIndex] (e : L ≃+ Translation 3)

def periodicTriangleProfileIso : Profile.S_X (physicalChecks K L e (checks K)) ≅
    (restrictedTriangle K (inclusionCoordinates L e)).obj₂ :=
  (physicalChecksRestrictionIso K L e (checks K)).symm ≪≫ (by
    simpa only [exampleRestriction, latticeMap_eq_coordinateEmbedding] using
      restrictedProfileIso K (inclusionCoordinates L e))

/-- The exact count holds for every finite-index period subgroup,
including skew periods, and tests the genuine restricted native class. -/
theorem periodic_count : logicalQudits L (checks K) (topological K) =
    if (couplingClass K).mapExactFunctor
      (ModuleCat.restrictScalars (latticeMap K (inclusionCoordinates L e))) = 0 then 6 else 4 := by
  rw [logicalQudits_eq_profile L e (checks K) (topological K),
    (homCoefficientsIso (probe K 3) (periodicTriangleProfileIso K L e)).toLinearEquiv.finrank_eq]
  exact restrictedTriangle_count K (inclusionCoordinates L e)

/-- For the literal L₁×L₂×L₃ torus, p dividing L₁L₂ is precisely the
six-logical-qudit case; otherwise exactly four survive. No positivity or
nondivisibility condition is imposed on the third period beyond L₃>0. -/
theorem rectangular_logicalQudits (p : ℕ) [Fact p.Prime]
    (periods : Fin 3 → ℕ) (hperiods : ∀ i, periods i ≠ 0) :
    logicalQudits (RectangularLattice.lattice periods) (checks (ZMod p)) (topological (ZMod p)) =
      if p ∣ periods 0 * periods 1 then 6 else 4 := by
  let := RectangularLattice.lattice_finiteIndex periods hperiods
  have h := periodic_count (ZMod p) (RectangularLattice.lattice periods)
    (RectangularLattice.coordinates periods hperiods)
  have he : inclusionCoordinates (RectangularLattice.lattice periods)
      (RectangularLattice.coordinates periods hperiods) = RectangularLattice.inclusion periods := by
    apply AddMonoidHom.ext
    intro x
    rfl
  rw [he, rectangular_coupling_zero_iff_dvd] at h
  by_cases hd : p ∣ periods 0 * periods 1
  · simpa only [ite_eq_left hd] using h
  · simpa only [ite_eq_right hd] using h

end
end Decoupling.HighDim.Glued
