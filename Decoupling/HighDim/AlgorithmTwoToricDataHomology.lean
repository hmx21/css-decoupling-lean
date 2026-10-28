import Decoupling.HighDim.AlgorithmTwoComparisonExistence

/-!
# Every solution of the prescribed comparison equations is a quasi-isomorphism

The top cells generate the actual homology of the toric stack. Hence
two chain maps agreeing on those cells induce identical maps on native
homology. The executable solver may return any solution of the stated
linear equations; no selection of a special quasi-isomorphism is needed.
-/
namespace Decoupling.HighDim.AlgorithmTwoToricData
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgorithmTwoComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
attribute [local instance] HasDerivedCategory.standard
variable {R : Type} [CommRing R]

theorem homologyMap_eq_of_component {A B : CochainComplex (ModuleCat R) ℤ}
    (f g : A ⟶ B) (n : ℤ) (he : f.f n = g.f n) : homologyMap f n = homologyMap g n := by
  have hc : cyclesMap f n = cyclesMap g n := by
    apply (cancel_mono (B.iCycles n)).mp
    rw [cyclesMap_i, cyclesMap_i, he]
  apply (cancel_epi (A.homologyπ n)).mp
  rw [homologyπ_naturality, homologyπ_naturality, hc]

variable (K : Type) [Field K] (D : ℕ)

theorem toricTop_spans (j : ℤ) (x : (Toric.model K D j).X j) :
    (toricTopEquiv K D j x) • toricTop K D j = x := by
  apply (toricTopEquiv K D j).injective
  simp [toricTop]

theorem individual_homologyMap_eq
    {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
    (j : ℤ) (f g : Toric.model K D j ⟶ C)
    (htop : f.f j (toricTop K D j) = g.f j (toricTop K D j)) (n : ℤ) :
    homologyMap f n = homologyMap g n := by
  by_cases hnj : n = j
  · subst n
    apply homologyMap_eq_of_component
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rw [← toricTop_spans K D j x, map_smul, map_smul, htop]
  · have hz : IsZero ((Toric.model K D j).homology n) := by
      rcases lt_or_gt_of_ne hnj with hn | hn
      · exact ((Toric.model K D j).exactAt_of_isGE j n hn).isZero_homology
      · exact (ExactAt.of_isZero ((Toric.model K D j).isZero_of_isStrictlyLE j n hn)).isZero_homology
    exact hz.eq_of_src _ _

variable {ι : Type} [Fintype ι] (forms : ι → ℕ)
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}

local instance toricDataHomologyFiniteBiproducts : HasFiniteBiproducts (CochainComplex (ModuleCat (Laurent K D)) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

theorem homologyMap_eq_of_top_values (f g : Toric.stackModel K D forms ⟶ C)
    (htop : ∀ i, f.f (forms i + 1) (stackTop K D forms i) =
      g.f (forms i + 1) (stackTop K D forms i)) (n : ℤ) :
    homologyMap f n = homologyMap g n := by
  let M := fun i => Toric.model K D (forms i + 1)
  let H := homologyFunctor (ModuleCat (Laurent K D)) (ComplexShape.up ℤ) n
  apply (cancel_epi (H.mapBiproduct M).inv).mp
  apply biproduct.hom_ext'
  intro i
  simp only [Functor.mapBiproduct_inv, ← Category.assoc, biproduct.ι_desc]
  change H.map (biproduct.ι M i) ≫ H.map f = H.map (biproduct.ι M i) ≫ H.map g
  rw [← H.map_comp, ← H.map_comp]
  exact individual_homologyMap_eq K D (forms i + 1) _ _ (htop i) n

theorem quasiIso_of_same_top_values (f g : Toric.stackModel K D forms ⟶ C) [QuasiIso f]
    (htop : ∀ i, f.f (forms i + 1) (stackTop K D forms i) =
      g.f (forms i + 1) (stackTop K D forms i)) : QuasiIso g := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap, ← homologyMap_eq_of_top_values K D forms f g htop]
  infer_instance

/-- Arbitrary solver output satisfying the prescribed top values is
a genuine quasi-isomorphism, because all such outputs have the same
native homology maps as the proved comparison witness. -/
theorem quasiIso_of_prescribed_values
    (e : DerivedCategory.Q.obj (Toric.stackModel K D forms) ≅ DerivedCategory.Q.obj C)
    (b : ∀ n, (stackZeroModel K D forms).X n ≅ C.homology n)
    (c : ∀ i, C.X (forms i + 1))
    (hc : ∀ i, C.d (forms i + 1) (((forms i : ℤ) + 1) + 1) (c i) = 0)
    (hclass : ∀ i, nativeCycleClass C (forms i + 1) (c i) (hc i) =
      (b (forms i + 1)).hom (stackTopImage K D forms i))
    (g : Toric.stackModel K D forms ⟶ C)
    (hg : ∀ i, g.f (forms i + 1) (stackTop K D forms i) = c i) : QuasiIso g := by
  obtain ⟨f, hf, htop⟩ := exists_prescribed_comparison K D forms e b c hc hclass
  let : QuasiIso f := hf
  apply quasiIso_of_same_top_values K D forms f g
  intro i
  rw [htop, hg]

end
end Decoupling.HighDim.AlgorithmTwoToricData
