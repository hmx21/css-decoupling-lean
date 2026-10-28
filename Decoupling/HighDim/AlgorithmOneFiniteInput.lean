import Decoupling.HighDim.AlgorithmOnePipelineBridge
import Decoupling.HighDim.ScalingLatticeChecks

/-!
# Finite free input terms follow from the original Algorithm 1 assumptions

The finite coset basis proves preservation under literal lattice
restriction. A ring-equivalence renaming then gives the displayed standard
Laurent coordinates. No freeness, projective splitting, new basis of a
Schanuel complement, or executable basis-selection claim is assumed.
The existential basis is not identified with physical qudit/coset labels;
the actual algorithm retains the caller's supplied physical coordinates.
-/
namespace Decoupling.HighDim.AlgorithmOneFiniteInput
open CategoryTheory LatticeRestriction ScalingLattice
open scoped ModuleCat.Algebra
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

section Rename
variable {A B : Type} [CommRing A] [CommRing B] (rho : A ≃+* B)
  (M : ModuleCat.{0} A) [Module.Finite A M] [Module.Free A M]

/-- Only a basis of the already finite-free input module is selected. -/
def renamedCoordinates :
    (RingChange.rename rho).obj M ≃ₗ[B]
      (Fin (Fintype.card (Fin (Fintype.card (Module.Free.ChooseBasisIndex A M)))) → B) :=
  (((RingChange.rename rho).mapIso (StableCokernel.finiteFreeEquiv M).toModuleIso).toLinearEquiv).trans
    (linearize rho (vectorRename (ι := Fin (Fintype.card (Module.Free.ChooseBasisIndex A M))) rho))

instance renamed_free : Module.Free B ((RingChange.rename rho).obj M) :=
  Module.Free.of_equiv (renamedCoordinates rho M).symm
instance renamed_finite : Module.Finite B ((RingChange.rename rho).obj M) :=
  Module.Finite.of_surjective (renamedCoordinates rho M).symm.toLinearMap
    (renamedCoordinates rho M).symm.surjective
end Rename

section Restriction
variable (K : Type) [CommRing K] {D : ℕ} (Λ : AddSubgroup (Translation D)) [Λ.FiniteIndex]
  (e : Λ ≃+ Translation D) (M : ModuleCat.{0} (Laurent K D))

/-- Identity of underlying elements with the actual retained scalar action. -/
def retainedEquiv : M ≃ₗ[S K Λ] ((LatticeExt.restriction K Λ).obj M) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance retained_free [Module.Free (Laurent K D) M] :
    Module.Free (S K Λ) ((LatticeExt.restriction K Λ).obj M) := by
  let : Module.Free (S K Λ) M := free_restrict_of_free K Λ M
  exact Module.Free.of_equiv (retainedEquiv K Λ M)

instance retained_finite [Module.Finite (Laurent K D) M] :
    Module.Finite (S K Λ) ((LatticeExt.restriction K Λ).obj M) := by
  let : Module.Finite (S K Λ) M := finite_restrict_of_finite K Λ M
  exact Module.Finite.of_surjective (retainedEquiv K Λ M).toLinearMap (retainedEquiv K Λ M).surjective

/-- Arbitrary finite-index retained lattices, including oblique lattices. -/
theorem coordinate_restriction_finite_free [Module.Finite (Laurent K D) M] [Module.Free (Laurent K D) M] :
    Module.Finite (Laurent K D) ((ModuleCat.restrictScalars (coordinateEmbedding K Λ e)).obj M) ∧
    Module.Free (Laurent K D) ((ModuleCat.restrictScalars (coordinateEmbedding K Λ e)).obj M) := by
  let f : ((ModuleCat.restrictScalars (coordinateEmbedding K Λ e)).obj M) ≃ₗ[Laurent K D]
      ((RingChange.rename (ringCoordinates K Λ e)).obj ((LatticeExt.restriction K Λ).obj M)) :=
    ((coordinateRestrictionIso K Λ e).app M).toLinearEquiv
  let hf : Module.Free (Laurent K D)
      ((RingChange.rename (ringCoordinates K Λ e)).obj ((LatticeExt.restriction K Λ).obj M)) := inferInstance
  let hfinite : Module.Finite (Laurent K D)
      ((RingChange.rename (ringCoordinates K Λ e)).obj ((LatticeExt.restriction K Λ).obj M)) := inferInstance
  exact ⟨Module.Finite.of_surjective f.symm.toLinearMap f.symm.surjective, Module.Free.of_equiv f.symm⟩
end Restriction
end
end Decoupling.HighDim.AlgorithmOneFiniteInput

namespace Decoupling.HighDim.AlgorithmOne
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {p D q s r : ℕ} [Fact p.Prime] (c : CSS.Checks (ZMod p) D q s r)

instance successComplex_finite (hc : c.Topological) (h : Layers.FiniteXLayers c) (j : ℤ) :
    Module.Finite (Laurent (ZMod p) D) ((successComplex c hc h).X j) := by
  let : (TheoremOne.lattice c).FiniteIndex := TheoremOne.lattice_finiteIndex c h
  exact (AlgorithmOneFiniteInput.coordinate_restriction_finite_free (ZMod p) (TheoremOne.lattice c)
    (TheoremOne.coordinates c h) ((FiniteResolution.cssComplex c hc).X j)).1

instance successComplex_free (hc : c.Topological) (h : Layers.FiniteXLayers c) (j : ℤ) :
    Module.Free (Laurent (ZMod p) D) ((successComplex c hc h).X j) := by
  let : (TheoremOne.lattice c).FiniteIndex := TheoremOne.lattice_finiteIndex c h
  exact (AlgorithmOneFiniteInput.coordinate_restriction_finite_free (ZMod p) (TheoremOne.lattice c)
    (TheoremOne.coordinates c h) ((FiniteResolution.cssComplex c hc).X j)).2

/-- Coordinates exist under precisely the original topological and finite-layer
conditions. This is existence for Algorithm 2's supplied input representation,
not an executable algorithm for choosing bases or a cost claim for Algorithm 1. -/
theorem successComplex_coordinates (hc : c.Topological) (h : Layers.FiniteXLayers c) :
    Nonempty (StableFree.Coordinates (successComplex c hc h)) :=
  ⟨StableFree.Coordinates.ofFiniteFree (successComplex c hc h)⟩

end
end Decoupling.HighDim.AlgorithmOne
