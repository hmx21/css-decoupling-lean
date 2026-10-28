import Decoupling.HighDim.PerfectModel

/-!
# Canonically chosen actual models for every adjacent truncation

These definitions apply at every integer degree, including degrees outside
the support. Their existence requires only the supplied finite support
and finite coefficient homology, and never trivial translation action.
-/
namespace Decoupling.HighDim.PerfectModel
open CategoryTheory CategoryTheory.Limits Torus PostnikovInduction PostnikovTruncation
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {D : ℕ}

theorem homology_finite (s : Finset ℤ) (X : Derived.{0} K D) (hX : Supported X s)
    (hfin : ∀ i ∈ s, Module.Finite (Laurent K D) (H X i)) (j : ℤ) :
    Module.Finite (Laurent K D) (H X j) := by
  by_cases hj : j ∈ s
  · exact hfin j hj
  · let : Subsingleton (H X j) := ModuleCat.subsingleton_of_isZero (hX j hj)
    exact Module.Finite.of_finite

theorem lower_exists (s : Finset ℤ) (X : Derived.{0} K D) (hX : Supported X s)
    (hfin : ∀ i ∈ s, Module.Finite (Laurent K D) (H X i)) (j : ℤ) :
    Nonempty (TensorModel (lower X j)) := by
  apply exists_of_supported (s.erase j) (lower X j) (lower_supported hX j)
  intro i hi
  by_cases hij : i < j
  · let := hfin i (Finset.mem_of_mem_erase hi)
    exact Module.Finite.equiv (lowerHomologyIso X j i hij).symm.toLinearEquiv
  · let : Subsingleton (H (lower X j) i) := ModuleCat.subsingleton_of_isZero
      (DerivedCategory.isZero_of_isLE (lower X j) (j - 1) i (by omega))
    exact Module.Finite.of_finite

variable (s : Finset ℤ) (X : Derived.{0} K D) (hX : Supported X s)
  (hfin : ∀ i ∈ s, Module.Finite K (Layers.coefficients (H X i)))

def wholeModel : TensorModel X :=
  Classical.choice (exists_of_finite_coefficients s X hX hfin)

def lowerModel (j : ℤ) : TensorModel (lower X j) :=
  Classical.choice (lower_exists s X hX (fun i hi => by
    let := hfin i hi
    exact finite_of_coefficients (H X i)) j)

def capModel (j : ℤ) : TensorModel (AdjacentGluing.cap X j) := lowerModel s X hX hfin (j + 1)

def layerModel (j : ℤ) :
    TensorModel ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj (H X j)) := by
  letI := homology_finite s X hX (fun i hi => by
    let := hfin i hi
    exact finite_of_coefficients (H X i)) j
  exact Classical.choice (single_exists (H X j) j)

/-- The third object of the actual raw adjacent triangle is identified
by its proved canonical homology-layer isomorphism. -/
def rawLayerModel (j : ℤ) : TensorModel (AdjacentGluing.rawTriangle X j).obj₃ :=
  ofIso (layerModel s X hX hfin j) (AdjacentGluing.layerIso X j).symm

end
end Decoupling.HighDim.PerfectModel
