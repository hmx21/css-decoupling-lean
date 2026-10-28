import Decoupling.HighDim.PerfectModelCones
import Decoupling.HighDim.AdjacentGluing

/-!
# Actual bounded free models for every finite supported coherent profile

Finite support and finite generation of its actual native homology suffice.
The induction attaches the actual connecting map using a lifted cochain
map and its mapping cone; no splitting or trivial action is assumed.
-/
namespace Decoupling.HighDim.PerfectModel
open CategoryTheory CategoryTheory.Limits Torus PostnikovInduction PostnikovTruncation
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] {D : ℕ}

/-- Finite coefficient dimension implies finite generation over the true
Laurent ring; the coefficient action is the actual restriction by constant. -/
theorem finite_of_coefficients (A : ModuleCat (Laurent K D))
    [h : Module.Finite K (Layers.coefficients A)] : Module.Finite (Laurent K D) A := by
  let : Module K A := Module.compHom A (constant : K →+* Laurent K D)
  let : Module K (Laurent K D) := Module.compHom (Laurent K D) (constant : K →+* Laurent K D)
  let : IsScalarTower K (Laurent K D) A := ⟨fun a r m => by
    rw [Algebra.smul_def]
    change (constant (D := D) a * r) • m = constant (D := D) a • r • m
    exact mul_smul _ _ _⟩
  let : Module.Finite K A := h
  exact Module.Finite.of_restrictScalars_finite K (Laurent K D) A

/-- Every finite-supported object whose actual homology modules are
finitely generated has a bounded finite-free Laurent model. -/
theorem exists_of_supported : ∀ (s : Finset ℤ) (X : Derived.{0} K D), Supported X s →
    (∀ i ∈ s, Module.Finite (Laurent K D) (H X i)) → Nonempty (TensorModel X) := by
  intro s
  refine Finset.strongInductionOn s (fun s ih => ?_)
  intro X hX hfin
  by_cases hs : s.Nonempty
  · let j := s.max' hs
    have hj : j ∈ s := Finset.max'_mem s hs
    have hle : ∀ i ∈ s, i ≤ j := fun i hi => Finset.le_max' s i hi
    have hlt : ∀ i ∈ s.erase j, i < j := by
      intro i hi
      have hi' := Finset.mem_erase.mp hi
      have := hle i hi'.2
      omega
    let : X.IsLE j := supported_isLE hX j hle
    obtain ⟨M⟩ := ih (s.erase j) (Finset.erase_ssubset hj) (lower X j)
      (lower_supported hX j) (fun i hi => by
        let := hfin i (Finset.mem_of_mem_erase hi)
        exact Module.Finite.equiv (lowerHomologyIso X j i (hlt i hi)).symm.toLinearEquiv)
    let := hfin j hj
    obtain ⟨N⟩ := single_exists (H X j) j
    exact ⟨middle (triangle X j) (t.triangleLTGE_distinguished j X) M
      (ofIso N (upperSingleIso X j).symm)⟩
  · have he : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    let : X.IsLE 0 := supported_isLE hX 0 (by simp)
    let : X.IsGE 1 := supported_isGE hX 1 (by simp)
    have hzX : IsZero X := t.isZero X 0 1
    let A := ModuleCat.of (Laurent K D) (Fin 0 → Laurent K D)
    let : Subsingleton A := inferInstanceAs (Subsingleton (Fin 0 → Laurent K D))
    let : Module.Finite (Laurent K D) A := Module.Finite.of_finite
    obtain ⟨M⟩ := single_exists A 0
    have hzA : IsZero A := ModuleCat.isZero_iff_subsingleton.mpr inferInstance
    have hz := (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) 0).map_isZero hzA
    exact ⟨ofIso M (hz.iso hzX)⟩

/-- In particular, finite coefficient layers give actual models without
assuming augmentation action or vanishing of any gluing. -/
theorem exists_of_finite_coefficients (s : Finset ℤ) (X : Derived.{0} K D) (hX : Supported X s)
    (hfin : ∀ i ∈ s, Module.Finite K (Layers.coefficients (H X i))) :
    Nonempty (TensorModel X) := by
  apply exists_of_supported s X hX
  intro i hi
  let := hfin i hi
  exact finite_of_coefficients (H X i)

/-- A chosen actual model; existence was proved by the cone induction above. -/
def ofSupported (s : Finset ℤ) (X : Derived.{0} K D) (hX : Supported X s)
    (hfin : ∀ i ∈ s, Module.Finite (Laurent K D) (H X i)) : TensorModel X :=
  Classical.choice (exists_of_supported s X hX hfin)

end
end Decoupling.HighDim.PerfectModel
