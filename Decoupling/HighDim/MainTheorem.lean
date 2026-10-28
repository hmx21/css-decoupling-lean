import Decoupling.HighDim.CorollaryOneZGeometry

/-!
# The high-dimensional decoupling theorem from one finite sector

This is the final one-sector interface for `drafts/main.tex`, Corollary 1.
The checks are actual finite Laurent matrices. The topological condition
contains both exactness equalities; the finite-layer hypothesis concerns
native Ext over the coefficient field in either one whole sector.

Each branch uses its own actual common translation kernel and precisely
p^(m-1) times that subgroup. All dimensions are the original t_j. The
Z branch includes the signed complementary dual-cell identification,
separately from the same-lattice finite SUM/SWAP circuit.
-/

namespace Decoupling.HighDim.MainTheorem

noncomputable section

variable {p D q s r : ℕ} [Fact p.Prime]
  (c : CSS.Checks (ZMod p) D q s r)

/-- X-sector decoupling on its literal finite-index lattice, with no
intermediate split-profile or circuit certificate supplied by the caller. -/
def XConclusion : Prop :=
  ∃ h : Layers.FiniteXLayers c, (TheoremOne.lattice c).FiniteIndex ∧
    Toric.DecouplesToStack (ZMod p) D
      (Toric.copyForms D (SplitMultiplicity.multiplicities c)) (CorollaryOne.coarseChecks c h)

/-- Z-sector decoupling to TC_(D-j), with the same original multiplicities
and an actual signed, translation-covariant complementary-cell map. -/
def ZConclusion : Prop :=
  ∃ h : Layers.FiniteZLayers c, (CorollaryOneZ.lattice c).FiniteIndex ∧
    Toric.DecouplesToComplementaryStack (ZMod p) D
      (Toric.copyForms D (CorollaryOneZ.multiplicities c))
      (CorollaryOneZ.complementaryForms c) (CorollaryOneZ.complementary_degree c)
      (CorollaryOneZ.coarseChecks c h) ∧
    Toric.DualGeometry (ZMod p) D
      (Toric.copyForms D (CorollaryOneZ.multiplicities c))
      (CorollaryOneZ.complementaryForms c) (CorollaryOneZ.complementary_degree c)

theorem decoupling_X (hc : c.Topological) (hD : 2 ≤ D) (h : Layers.FiniteXLayers c) :
    XConclusion c :=
  ⟨h, TheoremOne.lattice_finiteIndex c h, CorollaryOne.decouples_X c h hc hD⟩

theorem decoupling_Z (hc : c.Topological) (hD : 2 ≤ D) (h : Layers.FiniteZLayers c) :
    ZConclusion c :=
  ⟨h, CorollaryOneZ.lattice_finiteIndex c h,
    CorollaryOneZ.decouples_Z_with_geometry c h hc hD⟩

/-- Corollary 1 for arbitrary D≥2 and prime p. Apart from the finite local
translation-invariant CSS framework, the only code assumptions are the
two-sided topological condition and finite native Ext in one entire sector.
Zero layers, zero multiplicities and either prime characteristic are included. -/
theorem decoupling (hc : c.Topological) (hD : 2 ≤ D) (h : Layers.FiniteOneSector c) :
    XConclusion c ∨ ZConclusion c := by
  rcases h with h | h
  · exact Or.inl (decoupling_X c hc hD h)
  · exact Or.inr (decoupling_Z c hc hD h)

end
end Decoupling.HighDim.MainTheorem
