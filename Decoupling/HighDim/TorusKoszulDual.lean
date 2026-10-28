import Decoupling.HighDim.ToricNativeProfile
import Decoupling.HighDim.ToricHodgeExact

/-!
# Genuine self-duality of the full Laurent Koszul resolution

The ordinary Hom dual of the actual Koszul resolution of the augmentation
module is identified, including every signed differential, with the
reversed Koszul model concentrated in degrees zero through `D`. Its
augmentation is therefore a genuine quasi-isomorphism to `F[-D]`.
This is the ring-valued core of the torus local-duality comparison.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits HomologicalComplex Koszul
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (K : Type) [Field K] (D : ℕ)

abbrev dualKoszul : CochainComplex (ModuleCat (Laurent K D)) ℕ :=
  ResolutionCohomology.dualComplex (projectiveResolution K D)
    (ModuleCat.of (Laurent K D) (Laurent K D))

/-- Actual linear dual coordinates, without conjugating the coefficient
resolution. -/
def dualKoszulCoordinates (n : ℕ) : (dualKoszul K D).X n ≃ₗ[Laurent K D]
    Module.Dual (Laurent K D) (Term (Laurent K D) D n) := ModuleCat.homLinearEquiv

theorem dualKoszul_d_coordinates (n : ℕ) (f : (dualKoszul K D).X n) :
    dualKoszulCoordinates K D (n + 1) ((dualKoszul K D).d n (n + 1) f) =
      (boundary (Laurent K D) (difference K) n).hom.dualMap
        (dualKoszulCoordinates K D n f) := by
  change ((laurentComplex K D).d (n + 1) n ≫ f).hom = _
  simp only [laurentComplex, complex_d]
  rfl

theorem dualKoszul_isZero (n : ℕ) (hn : D < n) : IsZero ((dualKoszul K D).X n) := by
  let : Subsingleton (Term (Laurent K D) D n) := term_subsingleton (Laurent K D) hn
  let : Subsingleton ((dualKoszul K D).X n) := (dualKoszulCoordinates K D n).injective.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

/-- Signed complement on each actual Koszul term. -/
def dualKoszulComponent (n : ℕ) : (Toric.rightPart K D D).X n ≅ (dualKoszul K D).X n :=
  if hn : n ≤ D then
    Toric.rightPartTermIso K D D n (D - n) (by omega) ≪≫
      ((Toric.Hodge.duality (Laurent K D) (by omega : (D - n) + n = D)).trans
        (dualKoszulCoordinates K D n).symm).toModuleIso
  else
    ((Toric.model K D D).isZero_of_isStrictlyLE D n (by omega)).iso
      (dualKoszul_isZero K D n (by omega))

theorem dualKoszulComponent_coordinates (n b : ℕ) (hb : n + b = D)
    (x : (Toric.rightPart K D D).X n) :
    dualKoszulCoordinates K D n ((dualKoszulComponent K D n).hom x) =
      Toric.Hodge.duality (Laurent K D) (by omega : b + n = D)
        ((Toric.rightPartTermIso K D D n b (by omega)).hom x) := by
  have hn : n ≤ D := by omega
  have hb' : b = D - n := by omega
  subst b
  simp only [dualKoszulComponent, dite_eq_left hn]
  change dualKoszulCoordinates K D n
    ((dualKoszulCoordinates K D n).symm (Toric.Hodge.duality (Laurent K D) _
      ((Toric.rightPartTermIso K D D n (D - n) _).hom x))) = _
  exact (dualKoszulCoordinates K D n).apply_symm_apply _

theorem dualKoszulComponent_comm (n : ℕ) :
    (dualKoszulComponent K D n).hom ≫ (dualKoszul K D).d n (n + 1) =
      (Toric.rightPart K D D).d n (n + 1) ≫ (dualKoszulComponent K D (n + 1)).hom := by
  by_cases hn : n + 1 ≤ D
  · let b := D - (n + 1)
    have hb : n + b + 1 = D := by omega
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply (dualKoszulCoordinates K D (n + 1)).injective
    change dualKoszulCoordinates K D (n + 1)
      ((dualKoszul K D).d n (n + 1) ((dualKoszulComponent K D n).hom x)) =
        dualKoszulCoordinates K D (n + 1)
          ((dualKoszulComponent K D (n + 1)).hom ((Toric.rightPart K D D).d n (n + 1) x))
    rw [dualKoszul_d_coordinates, dualKoszulComponent_coordinates K D n (b + 1) (by omega),
      dualKoszulComponent_coordinates K D (n + 1) b (by omega),
      Toric.rightPart_d_coordinates K D 0 D n b hb]
    have he := congrArg (fun L => L ((Toric.rightPartTermIso K D D n (b + 1) (by omega)).hom x))
      (Toric.Hodge.duality_boundary (Laurent K D) (difference K)
        (by omega : b + 1 + n = D))
    exact he.symm
  · exact (dualKoszul_isZero K D (n + 1) (by omega)).eq_of_tgt _ _

/-- Self-duality as an isomorphism of complete actual cochain complexes. -/
def dualKoszulIso : Toric.rightPart K D D ≅ dualKoszul K D :=
  HomologicalComplex.Hom.isoOfComponents (dualKoszulComponent K D)
    (fun n m hnm => by
      change n + 1 = m at hnm
      subst m
      exact dualKoszulComponent_comm K D n)

/-- The full reversed model has no negative terms, so its nonnegative
inclusion is an actual chain isomorphism, including degree zero. -/
instance rightPartInclusion_top_isIso : IsIso (Toric.rightPartInclusion K D D) := by
  let : (Toric.model K D D).IsStrictlyGE 0 := by
    simpa using Toric.model_boundedBelow K D (D : ℤ)
  let : ∀ n : ℤ, IsIso ((Toric.rightPartInclusion K D D).f n) := by
    intro n
    cases n with
    | ofNat n => exact Toric.rightPartInclusion_isIso K D D n
    | negSucc n =>
      exact ((Toric.rightPart K D D).isZero_extend_X ComplexShape.embeddingUpNat
        (Int.negSucc n) (by intro k; simp)).isIso
        ((Toric.model K D D).isZero_of_isStrictlyGE 0 (Int.negSucc n) (by omega)) _
  exact HomologicalComplex.Hom.isIso_of_components _

/-- The full genuine RHom resolution complex is chain-isomorphic to the
signed reverse Koszul resolution. No positive truncation is inserted. -/
def rHomKoszulIso :
    Profile.rHomComplex (projectiveResolution K D)
      (ModuleCat.of (Laurent K D) (Laurent K D)) ≅ Toric.model K D D :=
  (ComplexShape.embeddingUpNat.extendFunctor (ModuleCat (Laurent K D))).mapIso
    (dualKoszulIso K D).symm ≪≫ asIso (Toric.rightPartInclusion K D D)

/-- `RHom_R(F,R) ≅ F[-D]` in the genuine derived category. The proof uses
actual signed complexes and the proved exact Koszul augmentation. -/
def rHomKoszulDerivedIso :
    DerivedCategory.Q.obj (Profile.rHomComplex (projectiveResolution K D)
      (ModuleCat.of (Laurent K D) (Laurent K D))) ≅
        (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) D).obj
          (coefficientModule K D) :=
  DerivedCategory.Q.mapIso (rHomKoszulIso K D) ≪≫ Toric.derivedIso K D D

end
end Decoupling.HighDim.Torus
