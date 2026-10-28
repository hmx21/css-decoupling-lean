import Decoupling.HighDim.TorusPostnikovFormal
import Decoupling.HighDim.TwoLayerCriterion

/-!
# Corollary 3: exact finite-torus counting and same-lattice decoupling

Source: HD008 main Corollary 3 and Appendix B.3. The logical-qudit count
is the dimension of the literal periodic CSS kernel/image quotient. The
period lattice is any finite-index subgroup, and the multiplicities are
those of the original native Ext modules. Equality itself forces this
lattice into the common translation kernel and forces every canonical
attachment to split. No extra coarse-graining occurs.
-/

namespace Decoupling.HighDim.Torus
open CategoryTheory CategoryTheory.Limits PostnikovInduction
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {p D q s r : ℕ} [Fact p.Prime]
  (L : AddSubgroup (Translation D)) [L.FiniteIndex] (e : L ≃+ Translation D)
  (c : CSS.Checks (ZMod p) D q s r)

/-- Equality of the actual finite-torus count with the binomial bound
forces actual stable SUM/SWAP decoupling on the very same period lattice. -/
theorem decouplesOn_of_maximalCount (hc : c.Topological) (hD : 1 ≤ D)
    (h : Layers.FiniteXLayers c) (heq : logicalQudits L c hc = layerBound c) :
    TwoLayer.DecouplesOn L e c := by
  have hL := maximalCount_le_commonKernel L e c hc hD h heq
  let X := TwoLayer.onLatticeProfile L e c
  have hdeg : ∀ i ∈ Profile.support c, 1 ≤ i ∧ i < D := by
    intro i hi
    obtain ⟨n, hn, hnD, _, rfl⟩ := (Profile.mem_support_iff c i).mp hi
    omega
  have hQ : ∀ i ∈ Profile.support c, FiniteAugmentation (H X i) := by
    intro i hi
    exact finiteAugmentation_of_iso
      (TwoLayer.onLatticeHomologyCoordinates L e c h hL ⟨i, hi⟩).symm
      (finiteAugmentation_coefficientVector (Layers.multiplicity c i.toNat))
  have hF : ∀ i ∈ Profile.support c,
      Module.Finite (ZMod p) (representedLayer (probe (ZMod p) D) X i) := by
    intro i hi
    let := (hQ i hi).1
    exact probeSingle_finite_int (H X i) i (hdeg i hi).1 (hdeg i hi).2
  have hsum : (∑ i ∈ Profile.support c,
      Module.finrank (ZMod p) (representedLayer (probe (ZMod p) D) X i)) = layerBound c := by
    rw [← finrank_hom_homologySum (probe (ZMod p) D) X (Profile.support c) hF]
    rw [(homCoefficientsIso (probe (ZMod p) D)
      (TwoLayer.onLatticeHomologyToToricIso L e c h hL)).toLinearEquiv.finrank_eq]
    exact finrank_multiplicity_splitTarget c
  have hcount : Module.finrank (ZMod p) (homCoefficients (probe (ZMod p) D) X) =
      logicalQudits L c hc := by
    rw [logicalQudits_eq_profile L e c hc]
    exact (homCoefficientsIso (probe (ZMod p) D)
      (ScalingLattice.physicalChecksRestrictionIso (ZMod p) L e c)).toLinearEquiv.finrank_eq
  apply TwoLayer.decouplesOn_of_formal L e c h hL hc
  apply probe_formal_of_maximal (Profile.support c) X
    (TwoLayer.onLattice_supported L e c hc hD) hdeg hQ
  rw [hcount, heq, hsum]

/-- The equality characterization is for the original multiplicities and
for exactly the given arbitrary finite-index lattice. -/
theorem logicalQudits_eq_iff_decouplesOn (hc : c.Topological) (hD : 1 ≤ D)
    (h : Layers.FiniteXLayers c) :
    logicalQudits L c hc = layerBound c ↔ TwoLayer.DecouplesOn L e c :=
  ⟨decouplesOn_of_maximalCount L e c hc hD h,
    maximalCount_of_decouplesOn L e c hc⟩

/-- Corollary 3 with a proved lattice basis selected internally, so its
only code assumptions are topology and finite-dimensional native Ext. -/
theorem corollary3 (hc : c.Topological) (hD : 2 ≤ D) (h : Layers.FiniteXLayers c) :
    logicalQudits L c hc ≤ layerBound c ∧
      (logicalQudits L c hc = layerBound c ↔
        TwoLayer.DecouplesOn L (LatticeBasis.coordinates L) c) := by
  exact ⟨logicalQudits_le L (LatticeBasis.coordinates L) c hc (by omega) h,
    logicalQudits_eq_iff_decouplesOn L (LatticeBasis.coordinates L) c hc (by omega) h⟩

end
end Decoupling.HighDim.Torus
