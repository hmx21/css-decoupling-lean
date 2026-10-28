import Decoupling.HighDim.AlgorithmTwoComparisonToric
import Decoupling.HighDim.AlgorithmTwoComparisonZeroModel

/-!
# The actual toric-stack augmentation to a zero-differential model

This is the direct sum of the already proved Koszul augmentations.
Its quasi-isomorphism and all zero differentials are proved, including
the empty stack and repeated degree indices.
-/
namespace Decoupling.HighDim.AlgorithmTwoComparison
open CategoryTheory CategoryTheory.Limits HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
attribute [local instance] HasDerivedCategory.standard
variable (K : Type) [Field K] (D : ℕ) {ι : Type} [Fintype ι] (forms : ι → ℕ)

local instance : HasFiniteBiproducts (CochainComplex (ModuleCat (Laurent K D)) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

def stackSingleFamily (i : ι) : CochainComplex (ModuleCat (Laurent K D)) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat (Laurent K D)) (forms i + 1)).obj
    (Koszul.coefficientModule K D)

def stackZeroModel : CochainComplex (ModuleCat (Laurent K D)) ℤ :=
  ⨁ stackSingleFamily K D forms

def stackAugmentation : Toric.stackModel K D forms ⟶ stackZeroModel K D forms :=
  biproduct.map (fun i => Toric.augmentation K D (forms i + 1))

theorem stackZeroModel_d (a b : ℤ) : (stackZeroModel K D forms).d a b = 0 := by
  let F := eval (ModuleCat (Laurent K D)) (ComplexShape.up ℤ) b
  apply (cancel_mono (F.mapBiproduct (stackSingleFamily K D forms)).hom).mp
  apply biproduct.hom_ext
  intro i
  simp only [Category.assoc, Functor.mapBiproduct_hom, zero_comp]
  dsimp +instances only [Function.comp_def]
  rw [biproduct.lift_π]
  change (stackZeroModel K D forms).d a b ≫
    (biproduct.π (stackSingleFamily K D forms) i).f b = 0
  dsimp only [stackZeroModel]
  rw [← (biproduct.π (stackSingleFamily K D forms) i).comm]
  simp [stackSingleFamily, CochainComplex.singleFunctor, HomologicalComplex.single_obj_d]

instance stackAugmentation_quasiIso : QuasiIso (stackAugmentation K D forms) := by
  let M := fun i => Toric.model K D (forms i + 1)
  let N := stackSingleFamily K D forms
  let F := DerivedCategory.Q (C := ModuleCat (Laurent K D))
  let e : F.obj (Toric.stackModel K D forms) ≅ F.obj (stackZeroModel K D forms) :=
    F.mapBiproduct M ≪≫ biproduct.mapIso (fun i => asIso (F.map (Toric.augmentation K D (forms i + 1)))) ≪≫
      (F.mapBiproduct N).symm
  have he : F.map (stackAugmentation K D forms) = e.hom := by
    apply (cancel_mono (F.mapBiproduct N).hom).mp
    dsimp only [e, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply biproduct.hom_ext
    intro i
    simp only [Category.assoc, Functor.mapBiproduct_hom, biproduct.mapIso_hom, asIso_hom]
    dsimp +instances only [Function.comp_def, M, N, stackZeroModel, Toric.stackModel,
      stackSingleFamily, stackAugmentation]
    rw [biproduct.lift_π, biproduct.map_π, ← Category.assoc, biproduct.lift_π]
    rw [← F.map_comp, biproduct.map_π, F.map_comp]
  apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat (Laurent K D)) _).mp
  change IsIso (F.map (stackAugmentation K D forms))
  rw [he]
  infer_instance

/-- Actual augmentation image of the distinguished top cell. -/
def stackTopImage (i : ι) : (stackZeroModel K D forms).X (forms i + 1) :=
  (stackAugmentation K D forms).f (forms i + 1) (stackTop K D forms i)

theorem stackAugmentation_class (i : ι) :
    homologyMap (stackAugmentation K D forms) (forms i + 1)
      (nativeCycleClass (Toric.stackModel K D forms) (forms i + 1)
        (stackTop K D forms i) (stackTop_closed K D forms i)) =
      (zeroClassIso (stackZeroModel K D forms) (stackZeroModel_d K D forms) (forms i + 1)).hom
        (stackTopImage K D forms i) := by
  rw [nativeCycleClass_naturality, zeroClassIso_apply]
  rfl

end
end Decoupling.HighDim.AlgorithmTwoComparison
