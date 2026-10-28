import Decoupling.HighDim.DecouplingCriterionZ
import Decoupling.HighDim.TorusSplitCount

/-!
# Finiteness is a consequence of the unrestricted criterion

An arbitrary actual toric split profile has finite coefficient homology.
Scalar restriction preserves the coefficient vector spaces. Thus finite
native X/Z layers follow from physical decoupling and are not assumptions
of HD010 Theorem 1.
-/
namespace Decoupling.HighDim.DecouplingCriterion
open CategoryTheory CategoryTheory.Limits PostnikovInduction
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {D : ℕ}

theorem singleHomology_finite (j n : ℤ) :
    Module.Finite K (Layers.coefficients
      (H ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj
        (Koszul.coefficientModule K D)) n)) := by
  let F := ModuleCat.restrictScalars (constant : K →+* Laurent K D)
  by_cases hn : n = j
  · subst n
    let e : Layers.coefficients
        (H ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj
          (Koszul.coefficientModule K D)) j) ≅ ModuleCat.of K K :=
      F.mapIso ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat (Laurent K D)) j).app (Koszul.coefficientModule K D)) ≪≫
        Torus.coefficientModuleCoefficientsIso
    exact Module.Finite.equiv e.symm.toLinearEquiv
  · have hz : IsZero (H ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj
        (Koszul.coefficientModule K D)) n) := by
      rcases lt_or_gt_of_ne hn with h | h
      · exact DerivedCategory.isZero_of_isGE _ j n h
      · exact DerivedCategory.isZero_of_isLE _ j n h
    let : Subsingleton (Layers.coefficients
      (H ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj
        (Koszul.coefficientModule K D)) n)) := ModuleCat.subsingleton_of_isZero (F.map_isZero hz)
    infer_instance

theorem splitHomology_finite {ι : Type} [Fintype ι] (forms : ι → ℕ) (n : ℤ) :
    Module.Finite K (Layers.coefficients (H (Toric.splitTarget K D forms) n)) := by
  let F := ModuleCat.restrictScalars (constant : K →+* Laurent K D)
  let M := fun i => H ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D))
    (forms i + 1)).obj (Koszul.coefficientModule K D)) n
  let : ∀ i, Module.Finite K (F.obj (M i)) := fun i => singleHomology_finite (forms i + 1) n
  let e : Layers.coefficients (H (Toric.splitTarget K D forms) n) ≅
      ModuleCat.of K (∀ i, F.obj (M i)) :=
    F.mapIso ((DerivedCategory.homologyFunctor (ModuleCat (Laurent K D)) n).mapBiproduct
      (fun i => (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) (forms i + 1)).obj
        (Koszul.coefficientModule K D))) ≪≫
      F.mapBiproduct M ≪≫ ModuleCat.biproductIsoPi (fun i => F.obj (M i))
  exact Module.Finite.equiv e.symm.toLinearEquiv

variable {p q s r : ℕ} [Fact p.Prime]
  (Λ : AddSubgroup (Translation D)) [Λ.FiniteIndex] (e : Λ ≃+ Translation D)
  (c : CSS.Checks (ZMod p) D q s r)

/-- Infinite-dimensional original layers obstruct decoupling on every
finite-index lattice; finiteness follows from the actual physical conclusion. -/
theorem finiteXLayers_of_decouples (hc : c.Topological) (hd : DecouplesOn Λ e c) :
    Layers.FiniteXLayers c := by
  obtain ⟨t, ⟨f⟩⟩ := (theorem1_X Λ e c hc).mp hd
  intro j hj _
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  let F := ModuleCat.restrictScalars (constant : ZMod p →+* Laurent (ZMod p) D)
  let eh := F.mapIso ((TwoLayer.onLatticeHomologyIso Λ e c n).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat (Laurent (ZMod p) D)) (n + 1 : ℕ)).mapIso f)
  let : Module.Finite (ZMod p) (F.obj (H (Toric.splitTarget (ZMod p) D
      (Toric.copyForms D t)) (n + 1 : ℕ))) :=
    splitHomology_finite (K := ZMod p) (D := D) (Toric.copyForms D t) (n + 1 : ℕ)
  let : Module.Finite (ZMod p)
      (Layers.coefficients ((TwoLayer.latticeRestriction Λ e).obj (Layers.layer c (n + 1)))) :=
    Module.Finite.equiv eh.symm.toLinearEquiv
  exact Module.Finite.equiv (TrivialLayers.coefficientRestrictionEquiv Λ e (Layers.layer c (n + 1)))

theorem finiteZLayers_of_decouples (hc : c.Topological) (hd : DecouplesOnZ Λ e c) :
    Layers.FiniteZLayers c := by
  apply finiteXLayers_of_decouples Λ e c.swap (c.topological_swap hc)
  exact (theorem1_X Λ e c.swap (c.topological_swap hc)).mpr ((theorem1_Z Λ e c hc).mp hd)

end
end Decoupling.HighDim.DecouplingCriterion
