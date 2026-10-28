import Decoupling.HighDim.SplitMultiplicity
import Decoupling.HighDim.ScalingLatticeProfile

/-!
# Theorem 1: exact-lattice splitting of the genuine CSS profile

Source: `drafts/main.tex`, Theorem 1. The inputs are the original two-sided
topological condition and finite positive Ext layers in the X sector.
The common-kernel lattice, its finite index, the exact p^(m-1) scaling,
the full derived splitting and every original multiplicity are constructed.
Natural subtraction covers m=0 and m=1 without any additional scaling.
-/

namespace Decoupling.HighDim.TheoremOne

open CategoryTheory ScalingLattice TrivialLayers
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {p D q s r : ℕ} [Fact p.Prime]
  (c : CSS.Checks (ZMod p) D q s r)

/-- The paper's literal subgroup of the original translation group. -/
def lattice : AddSubgroup (Translation D) :=
  LatticeBasis.finalLattice (Translations.lambda0 c) p (Layers.nonzeroLayerCount c)

variable (h : Layers.FiniteXLayers c)

include h in
theorem lattice_finiteIndex : (lattice c).FiniteIndex := by
  let := Translations.lambda0_finiteIndex c h
  exact LatticeBasis.finalLattice_finiteIndex (Translations.lambda0 c) (Fact.out : p.Prime) _

/-- The scaled original basis is a coordinate choice on the prescribed lattice. -/
def coordinates : lattice c ≃+ Translation D :=
  scaledCoordinates (Translations.lambda0 c) (lambda0Coordinates c h)
    (p ^ (Layers.nonzeroLayerCount c - 1))
    (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

def inclusion : Laurent (ZMod p) D →+* Laurent (ZMod p) D :=
  coordinateEmbedding (ZMod p) (lattice c) (coordinates c h)

/-- Actual scalar restriction of the full derived profile to the exact
retained lattice, expressed in its integer basis. -/
def restrictedProfile := (ModuleCat.restrictScalars (inclusion c h)).mapDerivedCategory.obj
  (Profile.S_X c)

def target := Toric.splitTarget (ZMod p) D
  (Toric.copyForms D (SplitMultiplicity.multiplicities c))

/-- Theorem 1, retaining every genuine derived extension until it has been
proved to vanish. No formality or translation triviality is an input. -/
theorem split (hc : c.Topological) (hD : 2 ≤ D) :
    Nonempty (restrictedProfile c h ≅ target c) := by
  obtain ⟨e⟩ := SplitMultiplicity.exists_multiplicity_split c h hc (by omega)
  exact ⟨(iteratedLatticeDerivedIso (ZMod p) (Translations.lambda0 c)
    (lambda0Coordinates c h) p (Layers.nonzeroLayerCount c - 1)
    (Fact.out : p.Prime).ne_zero).app (Profile.S_X c) ≪≫ e⟩

/-- The native profile computed from the actual coarse-grained physical
checks; only the coefficient ring is renamed by the same integer basis. -/
def physicalProfile : DerivedCategory (ModuleCat (Laurent (ZMod p) D)) := by
  letI := lattice_finiteIndex c h
  exact (ModuleCat.restrictScalars
    (ringCoordinates (ZMod p) (lattice c) (coordinates c h)).symm.toRingHom).mapDerivedCategory.obj
      (LatticeProfile.physicalProfile (ZMod p) (lattice c) c)

theorem physical_split (hc : c.Topological) (hD : 2 ≤ D) :
    Nonempty (physicalProfile c h ≅ target c) := by
  let := Translations.lambda0_finiteIndex c h
  obtain ⟨e⟩ := SplitMultiplicity.exists_multiplicity_split c h hc (by omega)
  exact ⟨(iteratedPhysicalProfileIso (ZMod p) (Translations.lambda0 c)
    (lambda0Coordinates c h) p (Layers.nonzeroLayerCount c - 1)
    (Fact.out : p.Prime).ne_zero c).symm ≪≫ e⟩

theorem lattice_one (hm : Layers.nonzeroLayerCount c = 1) : lattice c = Translations.lambda0 c := by
  simp only [lattice, hm, LatticeBasis.finalLattice_one]

theorem lattice_zero (hm : Layers.nonzeroLayerCount c = 0) : lattice c = ⊤ :=
  BoundaryCases.finalLattice_eq_top_of_no_layers c hm

end
end Decoupling.HighDim.TheoremOne
