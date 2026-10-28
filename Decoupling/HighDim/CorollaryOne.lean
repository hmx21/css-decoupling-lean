import Decoupling.HighDim.TheoremOne
import Decoupling.HighDim.ScalingLatticeChecksProfile

/-!
# Corollary 1: physical decoupling from the original X-sector hypotheses

The checks below are the literal coset expansion on the lattice of Theorem 1,
renamed by its integer basis. The native profile bridge connects that theorem
to Theorem 2. No split profile, comparison map or circuit is an input.
-/

namespace Decoupling.HighDim.CorollaryOne

open CategoryTheory ScalingLattice
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {p D q s r : ℕ} [Fact p.Prime]
  (c : CSS.Checks (ZMod p) D q s r) (h : Layers.FiniteXLayers c)

/-- The number of species in the actual retained-lattice coset basis. -/
def coarseCount (n : ℕ) : ℕ := by
  letI := TheoremOne.lattice_finiteIndex c h
  exact count (TheoremOne.lattice c) n

/-- The actual finite CSS checks on exactly p^(m-1) Lambda_0. -/
def coarseChecks : CSS.Checks (ZMod p) D
    (coarseCount c h q) (coarseCount c h s) (coarseCount c h r) := by
  letI := TheoremOne.lattice_finiteIndex c h
  exact physicalChecks (ZMod p) (TheoremOne.lattice c) (TheoremOne.coordinates c h) c

theorem coarseChecks_topological (hc : c.Topological) : (coarseChecks c h).Topological := by
  let := TheoremOne.lattice_finiteIndex c h
  exact physicalChecks_topological (ZMod p) (TheoremOne.lattice c)
    (TheoremOne.coordinates c h) c hc

/-- The full native derived profile of these actual checks is split with
the original, unscaled field dimensions t_j. -/
theorem coarseChecks_split (hc : c.Topological) (hD : 2 ≤ D) :
    Nonempty (Profile.S_X (coarseChecks c h) ≅ TheoremOne.target c) := by
  let := TheoremOne.lattice_finiteIndex c h
  obtain ⟨e⟩ := TheoremOne.split c h hc hD
  exact ⟨(physicalChecksRestrictionIso (ZMod p) (TheoremOne.lattice c)
    (TheoremOne.coordinates c h) c).symm ≪≫ e⟩

/-- Corollary 1, X sector: an actual finite, local, translation-invariant
SUM/SWAP word, with product ancillas and identity checks, transports both
stabilizer modules to the stated toric stack on the specified lattice.
Only the original two-sided topological condition and finite native Ext
layers in this one sector are assumed. -/
theorem decouples_X (hc : c.Topological) (hD : 2 ≤ D) :
    Toric.DecouplesToStack (ZMod p) D
      (Toric.copyForms D (SplitMultiplicity.multiplicities c)) (coarseChecks c h) := by
  obtain ⟨e⟩ := coarseChecks_split c h hc hD
  exact Toric.decouples_of_multiplicity_split (ZMod p) D
    (SplitMultiplicity.multiplicities c) (coarseChecks c h)
    (coarseChecks_topological c h hc) e

end
end Decoupling.HighDim.CorollaryOne
