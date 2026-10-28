import Decoupling.HighDim.AlgorithmOneSpecification
import Decoupling.HighDim.AlgorithmTwoOriginalArraysNative

/-!
# HD012 Algorithm 1 supplies the original hypotheses of Algorithm 2

The true restricted complex inherits the dimension-dependent native
bounds. Its toric formality is derived from the original two-sided
topological condition and finite dimensionality of the entire X side.
It is not an additional input assumption about the original code.

As with Algorithm 1's existing specification, this is a mathematical
bridge. The cost claim applies to the already supplied coarse-grained
adjacent arrays, not to computation of the coarse-graining lattice.
-/
namespace Decoupling.HighDim.AlgorithmOne
open CategoryTheory Matrix
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p D q s r : ℕ} [Fact p.Prime] (c : CSS.Checks (ZMod p) D q s r)

instance successComplex_strictlyGE (hc : c.Topological) (h : Layers.FiniteXLayers c) :
    (successComplex c hc h).IsStrictlyGE (-((D+2 : ℕ) : ℤ)) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro j hj
  exact (ModuleCat.restrictScalars (TheoremOne.inclusion c h)).map_isZero
    ((FiniteResolution.cssComplex c hc).isZero_of_isStrictlyGE (-((D+2 : ℕ) : ℤ)) j hj)

instance successComplex_strictlyLE (hc : c.Topological) (h : Layers.FiniteXLayers c) :
    (successComplex c hc h).IsStrictlyLE ((D+2 : ℕ) : ℤ) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro j hj
  exact (ModuleCat.restrictScalars (TheoremOne.inclusion c h)).map_isZero
    ((FiniteResolution.cssComplex c hc).isZero_of_isStrictlyLE ((D : ℤ)+2) j (by
      exact_mod_cast hj))

theorem successComplex_formal (hc : c.Topological) (hD : 2 ≤ D) (h : Layers.FiniteXLayers c) :
    ∃ old : Fin (D-1) → ℕ,
      Nonempty (DerivedCategory.Q.obj (Toric.stackModel (ZMod p) D (Toric.copyForms D old)) ≅
        DerivedCategory.Q.obj (successComplex c hc h)) := by
  obtain ⟨e⟩ := success c hc hD h
  exact ⟨SplitMultiplicity.multiplicities c,
    ⟨Toric.stackDerivedIso (ZMod p) D (Toric.copyForms D (SplitMultiplicity.multiplicities c)) ≪≫ e.symm⟩⟩

/-- The caller supplies only the original free coordinates and original
adjacent coefficient arrays, with their original meaning. Both boundedness
and toric formality are derived from the successful coarse-graining proof. -/
def successOriginalInput (hc : c.Topological) (hD : 2 ≤ D) (h : Layers.FiniteXLayers c)
    (coords : StableFree.Coordinates (successComplex c hc h)) {B : ℕ}
    (d : ∀ i : Fin (AlgorithmTwoPipeline.inputLength (D+2)),
      LaurentArithmetic.DenseMatrix (ZMod p) D
        (coords.rank (-((D+2 : ℕ) : ℤ)+i+1)) (coords.rank (-((D+2 : ℕ) : ℤ)+i)) B)
    (hd : ∀ (i : Fin (AlgorithmTwoPipeline.inputLength (D+2)))
      (x : (successComplex c hc h).X (-((D+2 : ℕ) : ℤ)+i)),
      LaurentArithmetic.matrixDenote (d i) *ᵥ coords.equiv (-((D+2 : ℕ) : ℤ)+i) x =
        coords.equiv (-((D+2 : ℕ) : ℤ)+i+1)
          (((successComplex c hc h).d (-((D+2 : ℕ) : ℤ)+i) (-((D+2 : ℕ) : ℤ)+i+1)).hom x)) :
    AlgorithmTwoOriginalArrays.Input (L := D+2) (h := B) coords where
  differential := d
  represents := hd
  formal := successComplex_formal c hc hD h

end
end Decoupling.HighDim.AlgorithmOne
