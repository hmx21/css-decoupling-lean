import Decoupling.HighDim.AlgorithmTwoComputedLayersNative
import Decoupling.HighDim.AlgorithmTwoToricDataHomology

/-!
# Rebuilding the formal toric model at the computed multiplicities

The original formal profile may use different, unspecified copy
indices. Degreewise native cohomology bases construct an actual
isomorphism between the zero-differential models, so the new stack's
formal equivalence is proved rather than supplied as a premise.
-/
namespace Decoupling.HighDim.AlgorithmTwoComputedLayers
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgorithmTwoComparison TrivialLayers
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
attribute [local instance] HasDerivedCategory.standard
variable (K : Type) [Field K] (D : ℕ)
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (old : Fin (D - 1) → ℕ)
  (e : DerivedCategory.Q.obj (Toric.stackModel K D (Toric.copyForms D old)) ≅ DerivedCategory.Q.obj C)
  (t : Fin (D - 1) → ℕ)
  (basis : ∀ j : Fin (D - 1), Module.Basis (Fin (t j)) K (Layers.coefficients (C.homology (j.val + 1))))

def computedZeroIso :
    stackZeroModel K D (Toric.copyForms D t) ≅ stackZeroModel K D (Toric.copyForms D old) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => nativeCoordinates K D old e t basis n ≪≫ (oldTermCohomologyIso K D old e n).symm)
    (by intro i j hij; simp [stackZeroModel_d])

/-- Genuine formality at the newly computed copy counts. There is no
assumption equating the old counts with the new ones. -/
def computedFormalIso :
    DerivedCategory.Q.obj (Toric.stackModel K D (Toric.copyForms D t)) ≅ DerivedCategory.Q.obj C :=
  asIso (DerivedCategory.Q.map (stackAugmentation K D (Toric.copyForms D t))) ≪≫
    DerivedCategory.Q.mapIso (computedZeroIso K D old e t basis) ≪≫
      (asIso (DerivedCategory.Q.map (stackAugmentation K D (Toric.copyForms D old)))).symm ≪≫ e

variable
  (cycle : ∀ j : Fin (D - 1), Fin (t j) → C.X (j.val + 1))
  (closed : ∀ j k, C.d (j.val + 1) ((j.val : ℤ) + 1 + 1) (cycle j k) = 0)
  (classes : ∀ j k, basis j k = nativeCycleClass C (j.val + 1) (cycle j k) (closed j k))

include old e basis closed classes in
theorem exists_computed_comparison :
    ∃ g : Toric.stackModel K D (Toric.copyForms D t) ⟶ C, QuasiIso g ∧
      ∀ (j : Fin (D - 1)) (k : Fin (t j)),
        g.f (j.val + 1) (stackTop K D (Toric.copyForms D t) ⟨j, k⟩) = cycle j k := by
  have hclass (i : Toric.Copies D t) :
      nativeCycleClass C (Toric.copyForms D t i + 1) (cycle i.1 i.2) (closed i.1 i.2) =
        (nativeCoordinates K D old e t basis (Toric.copyForms D t i + 1)).hom
          (stackTopImage K D (Toric.copyForms D t) i) := by
    rcases i with ⟨j, k⟩
    dsimp +instances only [Toric.copyForms]
    rw [nativeCoordinates_top, classes]
  obtain ⟨g, hg, htop⟩ := exists_prescribed_comparison K D (Toric.copyForms D t)
    (computedFormalIso K D old e t basis) (nativeCoordinates K D old e t basis)
    (fun i => cycle i.1 i.2) (fun i => closed i.1 i.2) hclass
  exact ⟨g, hg, fun j k => htop ⟨j, k⟩⟩

include old e basis closed classes in
theorem computed_solution_quasiIso
    (g : Toric.stackModel K D (Toric.copyForms D t) ⟶ C)
    (htop : ∀ (j : Fin (D - 1)) (k : Fin (t j)),
      g.f (j.val + 1) (stackTop K D (Toric.copyForms D t) ⟨j, k⟩) = cycle j k) : QuasiIso g := by
  obtain ⟨f, hf, hftop⟩ := exists_computed_comparison K D old e t basis cycle closed classes
  let : QuasiIso f := hf
  apply AlgorithmTwoToricData.quasiIso_of_same_top_values K D (Toric.copyForms D t) f g
  rintro ⟨j, k⟩
  dsimp +instances only [Toric.copyForms]
  rw [hftop, htop]

end
end Decoupling.HighDim.AlgorithmTwoComputedLayers
