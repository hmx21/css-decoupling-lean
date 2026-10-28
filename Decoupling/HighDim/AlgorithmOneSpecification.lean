import Decoupling.HighDim.PaperCorollaries
import Decoupling.HighDim.DecouplingCriterionFinite
import Decoupling.HighDim.FiniteResolutionProfile

/-!
# HD012 Algorithm 1: exact mathematical success and failure conditions

Source: main Algorithm 1 and the following correctness paragraph.
This module specifies and proves the two branches for the actual native
layers and actual restricted complex. It is not a claim that classical
choice is an executable finite-dimensionality decision algorithm.
-/
namespace Decoupling.HighDim.AlgorithmOne
open CategoryTheory DecouplingCriterion
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {p D q s r : ℕ} [Fact p.Prime] (c : CSS.Checks (ZMod p) D q s r)

/-- Actual physical decoupling on some finite-index subgroup. -/
def CanDecouple : Prop :=
  ∃ (Λ : AddSubgroup (Translation D)) (hΛ : Λ.FiniteIndex),
    ∃ e : Λ ≃+ Translation D, @DecouplesOn p D q s r _ Λ hΛ e c

/-- Algorithm 1 succeeds exactly when all layers are finite dimensional.
The necessity is for arbitrary retained lattices, not just the proposed one. -/
theorem canDecouple_iff_finite (hc : c.Topological) (hD : 2 ≤ D) :
    CanDecouple c ↔ Layers.FiniteXLayers c := by
  constructor
  · rintro ⟨Λ, hΛ, e, hd⟩
    let := hΛ
    exact finiteXLayers_of_decouples Λ e c hc hd
  · intro h
    let := TheoremOne.lattice_finiteIndex c h
    exact ⟨TheoremOne.lattice c, inferInstance, TheoremOne.coordinates c h,
      (Paper.corollary1_X c h hc hD).2⟩

/-- The rejection condition is an actual infinite-dimensional native
layer, and is equivalent to impossibility on every finite-index lattice. -/
theorem rejection_iff (hc : c.Topological) (hD : 2 ≤ D) :
    (∃ j : ℕ, 1 ≤ j ∧ j < D ∧
      ¬FiniteDimensional (ZMod p) (Layers.coefficients (Layers.layer c j))) ↔
        ¬CanDecouple c := by
  rw [canDecouple_iff_finite c hc hD, Layers.FiniteXLayers]
  push Not
  rfl

/-- The complex returned in the success branch is genuine restriction of
its input's actual finite-free model, not a newly computed profile. -/
def successComplex (hc : c.Topological) (h : Layers.FiniteXLayers c) :
    CochainComplex (ModuleCat (Laurent (ZMod p) D)) ℤ :=
  ((ModuleCat.restrictScalars (TheoremOne.inclusion c h)).mapHomologicalComplex (.up ℤ)).obj
    (FiniteResolution.cssComplex c hc)

def successComplex_profileIso (hc : c.Topological) (h : Layers.FiniteXLayers c) :
    DerivedCategory.Q.obj (successComplex c hc h) ≅ TheoremOne.restrictedProfile c h :=
  ((ModuleCat.restrictScalars (TheoremOne.inclusion c h)).mapDerivedCategoryFactors.app
    (FiniteResolution.cssComplex c hc)).symm ≪≫
      (ModuleCat.restrictScalars (TheoremOne.inclusion c h)).mapDerivedCategory.mapIso
        (FiniteResolution.cssComplex_profileIso c hc)

/-- Algorithm 1's precise successful output is split on the stated lattice. -/
theorem success (hc : c.Topological) (hD : 2 ≤ D) (h : Layers.FiniteXLayers c) :
    Nonempty (DerivedCategory.Q.obj (successComplex c hc h) ≅ TheoremOne.target c) := by
  obtain ⟨f⟩ := TheoremOne.split c h hc hD
  exact ⟨successComplex_profileIso c hc h ≪≫ f⟩

end
end Decoupling.HighDim.AlgorithmOne
