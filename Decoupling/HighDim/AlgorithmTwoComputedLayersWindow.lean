import Decoupling.HighDim.AlgorithmTwoCohomologyCorrectness
import Decoupling.HighDim.AlgorithmTwoComparisonCocycles

/-!
# Original degree-window coordinates and actual native cohomology

The matrices have exactly the ranks of the three supplied terms.
The two hypotheses state their actual action in those coordinates;
they are supplied by the verified per-degree dense slicing program.
No padded global matrix is substituted for a degree window.
-/
namespace Decoupling.HighDim.AlgorithmTwoComputedLayers
open CategoryTheory HomologicalComplex Matrix
open AlgorithmTwoComparison AlgorithmTwoCohomology CohomologyPresentation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
variable {K : Type} [Field K] {D : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (cC : StableFree.Coordinates C) (j : ℤ)
  (b : Matrix (Fin (cC.rank j)) (Fin (cC.rank (j - 1))) (Laurent K D))
  (d : Matrix (Fin (cC.rank (j + 1))) (Fin (cC.rank j)) (Laurent K D))
  (hb : ∀ x, b *ᵥ cC.equiv (j - 1) x = cC.equiv j (C.d (j - 1) j x))
  (hd : ∀ x, d *ᵥ cC.equiv j x = cC.equiv (j + 1) (C.d j (j + 1) x))

include hb hd in
theorem window_product_zero : d * b = 0 := by
  have ha (v : Fin (cC.rank (j - 1)) → Laurent K D) : d *ᵥ (b *ᵥ v) = 0 := by
    have h₁ := hb ((cC.equiv (j - 1)).symm v)
    rw [LinearEquiv.apply_symm_apply] at h₁
    rw [h₁, hd]
    change cC.equiv (j + 1)
      ((C.d (j - 1) j ≫ C.d j (j + 1)) ((cC.equiv (j - 1)).symm v)) = 0
    rw [C.d_comp_d]
    change cC.equiv (j + 1) 0 = 0
    exact map_zero _
  apply Matrix.ext
  intro i k
  have h := congrFun (ha (Pi.single k 1)) i
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_single_one] at h
  exact h

def coordinateWindowIso (hbd : d * b = 0) :
    C.sc' (j - 1) j (j + 1) ≅ window b d hbd :=
  ShortComplex.isoMk (cC.equiv (j - 1)).toModuleIso (cC.equiv j).toModuleIso
    (cC.equiv (j + 1)).toModuleIso
    (by apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; exact hb x)
    (by apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; exact hd x)

def windowNativeIso (hbd : d * b = 0) :
    (window b d hbd).homology ≅ C.homology j :=
  (ShortComplex.homologyFunctor (ModuleCat (Laurent K D))).mapIso
    (coordinateWindowIso cC j b d hb hd hbd).symm ≪≫ (cycleHomologyIso C j).symm

include hd in
theorem decoded_cycle_closed (v : Fin (cC.rank j) → Laurent K D) (hv : d *ᵥ v = 0) :
    C.d j (j + 1) ((cC.equiv j).symm v) = 0 := by
  apply (cC.equiv (j + 1)).injective
  rw [map_zero, ← hd, LinearEquiv.apply_symm_apply, hv]

theorem windowNativeIso_cycle (hbd : d * b = 0)
    (v : Fin (cC.rank j) → Laurent K D) (hv : d *ᵥ v = 0) :
    (windowNativeIso cC j b d hb hd hbd).hom (Glued.cycleClass (window b d hbd) v hv) =
      nativeCycleClass C j ((cC.equiv j).symm v) (decoded_cycle_closed cC j d hd v hv) := by
  change (cycleHomologyIso C j).inv
    (ShortComplex.homologyMap (coordinateWindowIso cC j b d hb hd hbd).inv
      (Glued.cycleClass (window b d hbd) v hv)) = _
  rw [Glued.homologyMap_cycleClass]
  rfl

def decodedCocycle {B : ℕ} (o : Result K D (cC.rank j) B) (k : Fin o.dimension) : C.X j :=
  (cC.equiv j).symm (o.cycle k)

include hb hd in
theorem correct_native_basis {B : ℕ} (hbd : d * b = 0)
    (o : Result K D (cC.rank j) B) (ho : Correct b d hbd o) :
    ∃ (closed : ∀ k, C.d j (j + 1) (decodedCocycle cC j o k) = 0),
      ∃ basis : Module.Basis (Fin o.dimension) K (Layers.coefficients (C.homology j)),
        ∀ k, basis k = nativeCycleClass C j (decodedCocycle cC j o k) (closed k) := by
  let closed := fun k => decoded_cycle_closed cC j d hd (o.cycle k) (ho.closed k)
  obtain ⟨basis, hbasis⟩ := ho.basis
  let e := (ModuleCat.restrictScalars (constant : K →+* Laurent K D)).mapIso
    (windowNativeIso cC j b d hb hd hbd)
  refine ⟨closed, basis.map e.toLinearEquiv, ?_⟩
  intro k
  change e.toLinearEquiv (basis k) = _
  rw [hbasis]
  exact windowNativeIso_cycle cC j b d hb hd hbd _ _

end
end Decoupling.HighDim.AlgorithmTwoComputedLayers
