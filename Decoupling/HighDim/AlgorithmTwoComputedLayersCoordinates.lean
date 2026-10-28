import Decoupling.HighDim.AlgorithmTwoComparisonTopCoordinate
import Decoupling.HighDim.SplitMultiplicity

/-!
# Grouped coordinates for the actual computed-multiplicity toric model

The grouped model has one coefficient vector space per permitted
degree. It is explicitly isomorphic to the individual-copy model
used by the actual toric stack, including zero multiplicities.
-/
namespace Decoupling.HighDim.AlgorithmTwoComputedLayers
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open AlgorithmTwoComparison TrivialLayers
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
variable (K : Type) [Field K] (D : ℕ) (t : Fin (D - 1) → ℕ)

local instance : HasFiniteBiproducts (CochainComplex (ModuleCat (Laurent K D)) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

def groupedFamily (j : Fin (D - 1)) : CochainComplex (ModuleCat (Laurent K D)) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat (Laurent K D)) (j.val + 1)).obj
    (coefficientVector K D (t j))

def groupedModel : CochainComplex (ModuleCat (Laurent K D)) ℤ := ⨁ groupedFamily K D t

def groupCopiesIso (j : Fin (D - 1)) :
    groupedFamily K D t j ≅
      ⨁ (fun _ : Fin (t j) =>
        (CochainComplex.singleFunctor (ModuleCat (Laurent K D)) (j.val + 1)).obj
          (Koszul.coefficientModule K D)) :=
  (CochainComplex.singleFunctor (ModuleCat (Laurent K D)) (j.val + 1)).mapIso
    (SplitMultiplicity.vectorIso K D (t j)) ≪≫
      (CochainComplex.singleFunctor (ModuleCat (Laurent K D)) (j.val + 1)).mapBiproduct _

def groupedCopiesIso :
    groupedModel K D t ≅ stackZeroModel K D (Toric.copyForms D t) :=
  biproduct.mapIso (groupCopiesIso K D t) ≪≫
    biproductBiproductIso (fun j : Fin (D - 1) => Fin (t j))
      (fun j _ => (CochainComplex.singleFunctor (ModuleCat (Laurent K D)) (j.val + 1)).obj
        (Koszul.coefficientModule K D))

def groupDegreeIso (j : Fin (D - 1)) :
    coefficientVector K D (t j) ≅ (groupedModel K D t).X (j.val + 1) :=
  (singleObjXSelf (ComplexShape.up ℤ) (j.val + 1) (coefficientVector K D (t j))).symm ≪≫
    mapBiproductInclusionIso (eval (ModuleCat (Laurent K D)) (ComplexShape.up ℤ) (j.val + 1))
      (groupedFamily K D t) j (by
        intro k hkj
        change IsZero (((CochainComplex.singleFunctor (ModuleCat (Laurent K D)) (k.val + 1)).obj
          (coefficientVector K D (t k))).X (j.val + 1))
        apply isZero_single_obj_X
        intro h
        apply hkj
        apply Fin.ext
        omega)

/-- Native Laurent-linear coordinates of the individual-copy model
at a supported degree. -/
def supportedCoordinates (j : Fin (D - 1)) :
    (stackZeroModel K D (Toric.copyForms D t)).X (j.val + 1) ≅ coefficientVector K D (t j) :=
  ((eval (ModuleCat (Laurent K D)) (ComplexShape.up ℤ) (j.val + 1)).mapIso
    (groupedCopiesIso K D t)).symm ≪≫ (groupDegreeIso K D t j).symm

theorem groupedModel_outside (n : ℤ) (hn : ¬ ∃ j : Fin (D - 1), (j.val : ℤ) + 1 = n) :
    IsZero ((groupedModel K D t).X n) := by
  let F := eval (ModuleCat (Laurent K D)) (ComplexShape.up ℤ) n
  have hi (j : Fin (D - 1)) : IsZero (F.obj (groupedFamily K D t j)) := by
    change IsZero (((CochainComplex.singleFunctor (ModuleCat (Laurent K D)) (j.val + 1)).obj
      (coefficientVector K D (t j))).X n)
    apply isZero_single_obj_X
    exact fun (he : n = (j.val : ℤ) + 1) => hn ⟨j, he.symm⟩
  let (j : Fin (D - 1)) : Subsingleton (F.obj (groupedFamily K D t j)) :=
    ModuleCat.subsingleton_of_isZero (hi j)
  let e : (groupedModel K D t).X n ≅
      ModuleCat.of (Laurent K D) (∀ j, F.obj (groupedFamily K D t j)) :=
    F.mapBiproduct (groupedFamily K D t) ≪≫ ModuleCat.biproductIsoPi _
  exact (ModuleCat.isZero_of_subsingleton _).of_iso e

theorem stackZeroModel_outside (n : ℤ)
    (hn : ¬ ∃ j : Fin (D - 1), (j.val : ℤ) + 1 = n) :
    IsZero ((stackZeroModel K D (Toric.copyForms D t)).X n) :=
  (groupedModel_outside K D t n hn).of_iso
    ((eval (ModuleCat (Laurent K D)) (ComplexShape.up ℤ) n).mapIso (groupedCopiesIso K D t)).symm

end
end Decoupling.HighDim.AlgorithmTwoComputedLayers
