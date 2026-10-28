import Decoupling.HighDim.SchreyerPaperModel
import Decoupling.HighDim.AlgorithmOneFiniteInput

/-!
# HD014 Algorithm 1: genuine restriction of the new Schreyer CSS model

The successfully restricted complex is the literal scalar restriction of
`SchreyerCSS.model`. Its full native profile is split using the original
two-sided topology and finite X-layer hypotheses. Explicit finite powers
and the finite coset basis establish finite freeness after restriction.
No legacy finite-resolution CSS model is substituted for the new model.
This is a mathematical success theorem, not an executable Algorithm 1 or
an assertion that arbitrary selected degree-zero bases are physical labels.
-/
namespace Decoupling.HighDim.SchreyerAlgorithmOne
open CategoryTheory Matrix
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {p D q s r : ℕ} [Fact p.Prime] (c : CSS.Checks (ZMod p) D q s r)

/-- Actual restriction of the actual newly constructed bounded CSS model. -/
def successComplex (hc : c.Topological) (h : Layers.FiniteXLayers c) :
    CochainComplex (ModuleCat (Laurent (ZMod p) D)) ℤ :=
  ((ModuleCat.restrictScalars (TheoremOne.inclusion c h)).mapHomologicalComplex (.up ℤ)).obj
    (SchreyerCSS.model c hc)

def successComplex_profileIso (hc : c.Topological) (h : Layers.FiniteXLayers c) :
    DerivedCategory.Q.obj (successComplex c hc h) ≅ TheoremOne.restrictedProfile c h :=
  ((ModuleCat.restrictScalars (TheoremOne.inclusion c h)).mapDerivedCategoryFactors.app
    (SchreyerCSS.model c hc)).symm ≪≫
      (ModuleCat.restrictScalars (TheoremOne.inclusion c h)).mapDerivedCategory.mapIso
        (SchreyerCSS.model_profileIso c hc)

/-- The whole restricted native profile is split, including all extension data. -/
theorem success (hc : c.Topological) (hD : 2 ≤ D) (h : Layers.FiniteXLayers c) :
    Nonempty (DerivedCategory.Q.obj (successComplex c hc h) ≅ TheoremOne.target c) := by
  obtain ⟨f⟩ := TheoremOne.split c h hc hD
  exact ⟨successComplex_profileIso c hc h ≪≫ f⟩

instance successComplex_strictlyGE (hc : c.Topological) (h : Layers.FiniteXLayers c) :
    (successComplex c hc h).IsStrictlyGE (-((D+2 : ℕ) : ℤ)) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro j hj
  exact (ModuleCat.restrictScalars (TheoremOne.inclusion c h)).map_isZero
    ((SchreyerCSS.model c hc).isZero_of_isStrictlyGE (-((D+2 : ℕ) : ℤ)) j hj)

theorem successComplex_strictlyLE (hc : c.Topological) (h : Layers.FiniteXLayers c)
    (hD : 1 ≤ D) : (successComplex c hc h).IsStrictlyLE ((D+2 : ℕ) : ℤ) := by
  let : (SchreyerCSS.model c hc).IsStrictlyLE ((D : ℤ)+2) :=
    SchreyerCSS.model_boundedAbove c hc hD
  rw [CochainComplex.isStrictlyLE_iff]
  intro j hj
  exact (ModuleCat.restrictScalars (TheoremOne.inclusion c h)).map_isZero
    ((SchreyerCSS.model c hc).isZero_of_isStrictlyLE ((D : ℤ)+2) j (by exact_mod_cast hj))

instance successComplex_finite (hc : c.Topological) (h : Layers.FiniteXLayers c) (j : ℤ) :
    Module.Finite (Laurent (ZMod p) D) ((successComplex c hc h).X j) := by
  let : (TheoremOne.lattice c).FiniteIndex := TheoremOne.lattice_finiteIndex c h
  exact (AlgorithmOneFiniteInput.coordinate_restriction_finite_free (ZMod p) (TheoremOne.lattice c)
    (TheoremOne.coordinates c h) ((SchreyerCSS.model c hc).X j)).1

instance successComplex_free (hc : c.Topological) (h : Layers.FiniteXLayers c) (j : ℤ) :
    Module.Free (Laurent (ZMod p) D) ((successComplex c hc h).X j) := by
  let : (TheoremOne.lattice c).FiniteIndex := TheoremOne.lattice_finiteIndex c h
  exact (AlgorithmOneFiniteInput.coordinate_restriction_finite_free (ZMod p) (TheoremOne.lattice c)
    (TheoremOne.coordinates c h) ((SchreyerCSS.model c hc).X j)).2

/-- Coordinates exist for the already proved finite-free restricted terms. -/
theorem successComplex_coordinates (hc : c.Topological) (h : Layers.FiniteXLayers c) :
    Nonempty (StableFree.Coordinates (successComplex c hc h)) :=
  ⟨StableFree.Coordinates.ofFiniteFree (successComplex c hc h)⟩

theorem successComplex_formal (hc : c.Topological) (hD : 2 ≤ D) (h : Layers.FiniteXLayers c) :
    ∃ old : Fin (D-1) → ℕ,
      Nonempty (DerivedCategory.Q.obj (Toric.stackModel (ZMod p) D (Toric.copyForms D old)) ≅
        DerivedCategory.Q.obj (successComplex c hc h)) := by
  obtain ⟨e⟩ := success c hc hD h
  exact ⟨SplitMultiplicity.multiplicities c,
    ⟨Toric.stackDerivedIso (ZMod p) D (Toric.copyForms D (SplitMultiplicity.multiplicities c)) ≪≫ e.symm⟩⟩

end
end Decoupling.HighDim.SchreyerAlgorithmOne
