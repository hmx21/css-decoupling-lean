import Decoupling.HighDim.TorusHomotopyDual

/-!
# The zero-degree Koszul resolution and its actual ordinary dual

This identifies the degree-reversing dual of the complete Koszul model
with the complete derived-Hom cochain model constructed previously.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits HomologicalComplex Koszul
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (D : ℕ)

abbrev coefficientResolution := Toric.model K D 0

abbrev coefficientDualModel :=
  Profile.rHomComplex (projectiveResolution K D) (ModuleCat.of (Laurent K D) (Laurent K D))

instance coefficientResolutionDual_boundedBelow :
    (complexDual (Laurent K D) (coefficientResolution K D)).IsStrictlyGE 0 := by
  simpa using complexDual_boundedBelow (coefficientResolution K D) 0

def coefficientResolutionCoordinates (n : ℕ) :
    (coefficientResolution K D).X (-(n : ℤ)) ≅
      ModuleCat.of (Laurent K D) (Term (Laurent K D) D n) :=
  (laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE 0) (by simp)

def coefficientDualCoordinates (n : ℕ) :
    (coefficientDualModel K D).X n ≅ (dualKoszul K D).X n :=
  (dualKoszul K D).extendXIso ComplexShape.embeddingUpNat rfl

def coefficientDualComponent (n : ℤ) :
    (complexDual (Laurent K D) (coefficientResolution K D)).X n ≅
      (coefficientDualModel K D).X n :=
  if hn : 0 ≤ n then
    (complexDual (Laurent K D) (coefficientResolution K D)).XIsoOfEq
      (Int.toNat_of_nonneg hn).symm ≪≫
      ((coefficientResolutionCoordinates K D n.toNat).toLinearEquiv.symm.dualMap.trans
        (dualKoszulCoordinates K D n.toNat).symm).toModuleIso ≪≫
      (coefficientDualCoordinates K D n.toNat).symm ≪≫
      (coefficientDualModel K D).XIsoOfEq (Int.toNat_of_nonneg hn)
  else
    ((complexDual (Laurent K D) (coefficientResolution K D)).isZero_of_isStrictlyGE
      0 n (by omega)).iso
      ((dualKoszul K D).isZero_extend_X ComplexShape.embeddingUpNat n (by
        intro k hk
        change (k : ℤ) = n at hk
        omega))

theorem coefficientDualComponent_nat (n : ℕ) :
    coefficientDualComponent K D n =
      ((coefficientResolutionCoordinates K D n).toLinearEquiv.symm.dualMap.trans
        (dualKoszulCoordinates K D n).symm).toModuleIso ≪≫
      (coefficientDualCoordinates K D n).symm := by
  simp [coefficientDualComponent]

theorem coefficientResolution_d (n : ℕ) :
    (coefficientResolution K D).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (coefficientResolutionCoordinates K D (n + 1)).hom ≫
        boundary (Laurent K D) (difference K) n ≫
          (coefficientResolutionCoordinates K D n).inv := by
  simpa only [coefficientResolutionCoordinates, coefficientResolution, Toric.model,
    laurentComplex, complex_d] using
    (laurentComplex K D).extend_d_eq (ComplexShape.embeddingUpIntLE 0)
      (i := n + 1) (j := n) (i' := -((n + 1 : ℕ) : ℤ)) (j' := -(n : ℤ))
      (by simp) (by simp)

theorem coefficientDual_d (n : ℕ) :
    (coefficientDualModel K D).d n (n + 1 : ℕ) =
      (coefficientDualCoordinates K D n).hom ≫
        (dualKoszul K D).d n (n + 1) ≫
          (coefficientDualCoordinates K D (n + 1)).inv :=
  (dualKoszul K D).extend_d_eq ComplexShape.embeddingUpNat rfl rfl

theorem coefficientDualComponent_comm (n m : ℤ) (h : n + 1 = m) :
    (coefficientDualComponent K D n).hom ≫ (coefficientDualModel K D).d n m =
      (complexDual (Laurent K D) (coefficientResolution K D)).d n m ≫
        (coefficientDualComponent K D m).hom := by
  by_cases hn : 0 ≤ n
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    subst m
    rw [show (n : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by omega,
      coefficientDualComponent_nat, coefficientDualComponent_nat, coefficientDual_d]
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← cancel_mono (coefficientDualCoordinates K D (n + 1)).hom]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro l
    apply (dualKoszulCoordinates K D (n + 1)).injective
    apply LinearMap.ext
    intro x
    change l ((coefficientResolutionCoordinates K D n).inv
      ((laurentComplex K D).d (n + 1) n x)) =
      l ((coefficientResolution K D).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ))
        ((coefficientResolutionCoordinates K D (n + 1)).inv x))
    rw [coefficientResolution_d]
    simp [laurentComplex, complex_d]


  · exact ((complexDual (Laurent K D) (coefficientResolution K D)).isZero_of_isStrictlyGE
      0 n (by omega)).eq_of_src _ _

/-- Complete ordinary dual of the zero-degree Koszul resolution. -/
def coefficientResolutionDualIso :
    complexDual (Laurent K D) (coefficientResolution K D) ≅ coefficientDualModel K D :=
  HomologicalComplex.Hom.isoOfComponents (coefficientDualComponent K D)
    (fun n m h => coefficientDualComponent_comm K D n m h)

/-- Its native derived object is the coefficient module in degree `D`. -/
def coefficientResolutionDualDerivedIso :
    DerivedCategory.Q.obj (complexDual (Laurent K D) (coefficientResolution K D)) ≅
      (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) D).obj
        (coefficientModule K D) :=
  DerivedCategory.Q.mapIso (coefficientResolutionDualIso K D) ≪≫
    rHomKoszulDerivedIso K D

instance coefficientResolutionDual_boundedAbove :
    (complexDual (Laurent K D) (coefficientResolution K D)).IsStrictlyLE D := by
  simpa using complexDual_boundedAbove (coefficientResolution K D) (0 - D)

instance coefficientResolutionDual_kProjective :
    (complexDual (Laurent K D) (coefficientResolution K D)).IsKProjective :=
  CochainComplex.isKProjective_of_projective _ D

end
end Decoupling.HighDim.Torus
