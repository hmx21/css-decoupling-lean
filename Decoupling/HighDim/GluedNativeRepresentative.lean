import Decoupling.HighDim.GluedNativeShift

/-!
# The coupling map is the native Ext representative

This equality compares the actual placed coupling to mathlib's native
projective-resolution representative, including the native shift signs.
-/
namespace Decoupling.HighDim.Glued
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open HomologicalComplex Koszul KoszulExtFunctor
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

def shiftedCouplingTargetIso :
    ((CochainComplex.singleFunctor (ModuleCat (Laurent K 3)) 1).obj (coefficientModule K 3))⟦(3 : ℤ)⟧ ≅
      ((CochainComplex.singleFunctor (ModuleCat (Laurent K 3)) 0).obj (coefficientModule K 3))⟦(2 : ℤ)⟧ :=
  ((CochainComplex.singleFunctors (ModuleCat (Laurent K 3))).shiftIso 3 (-2) 1 (by norm_num)).app _ ≪≫
    (((CochainComplex.singleFunctors (ModuleCat (Laurent K 3))).shiftIso 2 (-2) 0 (by norm_num)).app _).symm

/-- Literal equality of the actual shifted coupling and the native
Ext² cocycle, through the explicit sign-correct resolution isomorphism. -/
theorem shiftedCoupling_representative :
    (shiftedResolutionIso K).hom ≫ (couplingToSingle K)⟦(3 : ℤ)⟧' ≫
      (shiftedCouplingTargetIso K).hom =
    representative (projectiveResolution K 3) (couplingCochain K) (couplingCochain_boundary K) := by
  ext i : 1
  by_cases hi : i = -2
  · subst i
    simp only [HomologicalComplex.comp_f, CochainComplex.shiftFunctor_map_f']
    change (shiftedResolutionIso K).hom.f (-2) ≫ (couplingToSingle K).f 1 ≫
      (shiftedCouplingTargetIso K).hom.f (-2) = _
    rw [couplingToSingle_f_one]
    have he : (shiftedResolutionIso K).hom.f (-2) =
        ((projectiveResolution K 3).cochainComplexXIso (-2) 2 rfl).hom ≫
          (Toric.termIso K 3 3 2).inv := by
      change (shiftedResolutionTermIso K (-2)).hom = _
      simpa [Toric.termIso, show Int.negOnePow 2 = 1 from rfl] using congrArg Iso.hom (shiftedResolutionTermIso_nat K 2)
    rw [he]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    erw [ExtValuesFunctor.representative_component (projectiveResolution K 3)
      (couplingCochain K) (couplingCochain_boundary K)]
    simp [shiftedCouplingTargetIso, CochainComplex.singleFunctors,
      CochainComplex.shiftFunctorObjXIso, singleObjXSelf, HomologicalComplex.XIsoOfEq,
      eqToIso, singleObjXIsoOfEq]
  · apply (isZero_single_obj_X (.up ℤ) 0 (coefficientModule K 3) (i+2) (by omega)).eq_of_tgt

/-- The native Ext hom of the displayed coupling is the localization of
its actual placed chain map, using explicit source and target isomorphisms.
This also fixes the class's ordered-cell table to `(-1,0,0)`. -/
theorem couplingClass_hom_actual :
    (couplingClass K).hom =
      (DerivedCategory.singleFunctorIsoCompQ (ModuleCat (Laurent K 3)) 0).hom.app
        (coefficientModule K 3) ≫
      inv (DerivedCategory.Q.map (projectiveResolution K 3).π') ≫
      DerivedCategory.Q.map ((shiftedResolutionIso K).hom ≫ (couplingToSingle K)⟦(3 : ℤ)⟧' ≫
        (shiftedCouplingTargetIso K).hom) ≫
      (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app
        ((CochainComplex.singleFunctor (ModuleCat (Laurent K 3)) 0).obj (coefficientModule K 3)) ≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat (Laurent K 3)) 0).inv.app
        (coefficientModule K 3))⟦(2 : ℤ)⟧' := by
  rw [shiftedCoupling_representative]
  change ((projectiveResolution K 3).extMk (couplingCochain K) 3 rfl (couplingCochain_boundary K)).hom = _
  rw [ProjectiveResolution.extMk_hom]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, ShiftedHom.map, Category.assoc]
  rfl

end
end Decoupling.HighDim.Glued
