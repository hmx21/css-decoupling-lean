import Decoupling.HighDim.ToricTailDualModel
import Decoupling.HighDim.ResolutionComparison

/-!
# The native positive derived profile of each actual higher-form toric code

Source: `drafts/main.tex`, the toric-profile calculation following the
finite free model of `𝒮_X`.

The actual resolution of the conjugated reduced module is dualized and
identified with the nonnegative half of the full signed Koszul model.
Canonical good truncation then proves an isomorphism of derived objects,
including their gluing data, to the coefficient module in the stated degree.
-/

namespace Decoupling.HighDim.Toric

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex

noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [CommRing K] [IsDomain K] (D j : ℕ)

omit [IsDomain K] in
def rightPartInclusion : (rightPart K D j).extend ComplexShape.embeddingUpNat ⟶ model K D j where
  f
    | .ofNat n => ((rightPart K D j).extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom
    | .negSucc _ => 0
  comm' i l hil := by
    change i + 1 = l at hil
    subst l
    cases i with
    | ofNat n =>
      change ((rightPart K D j).extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom ≫
          (rightPart K D j).d n (n + 1) =
        ((rightPart K D j).extend ComplexShape.embeddingUpNat).d (n : ℤ) (n + 1 : ℕ) ≫
          ((rightPart K D j).extendXIso ComplexShape.embeddingUpNat (i := n + 1) rfl).hom
      rw [(rightPart K D j).extend_d_eq ComplexShape.embeddingUpNat
        (i := n) (j := n + 1) (i' := (n : ℤ)) (j' := ((n + 1 : ℕ) : ℤ)) rfl rfl]
      simp
    | negSucc n =>
      exact ((rightPart K D j).isZero_extend_X ComplexShape.embeddingUpNat (Int.negSucc n)
        (by intro k; simp)).eq_of_src _ _

omit [IsDomain K] in
instance rightPartInclusion_isIso (n : ℕ) : IsIso ((rightPartInclusion K D j).f n) := by
  change IsIso ((rightPart K D j).extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom
  infer_instance

omit [IsDomain K] in
theorem rightPartInclusion_quasiIsoAt (n : ℕ) :
    QuasiIsoAt (rightPartInclusion K D j) (n + 1 : ℕ) := by
  rw [quasiIsoAt_iff' (rightPartInclusion K D j) (n : ℤ)
    (n + 1 : ℕ) (n + 2 : ℕ) (by simp) (by simp; omega)]
  let f := (shortComplexFunctor' (ModuleCat (Laurent K D)) (ComplexShape.up ℤ)
      (n : ℕ) (n + 1 : ℕ) (n + 2 : ℕ)).map (rightPartInclusion K D j)
  let : IsIso f.τ₁ := rightPartInclusion_isIso K D j n
  let : IsIso f.τ₂ := rightPartInclusion_isIso K D j (n + 1)
  let : IsIso f.τ₃ := rightPartInclusion_isIso K D j (n + 2)
  let : IsIso f := ShortComplex.isIso_of_isIso f
  change ShortComplex.QuasiIso f
  infer_instance

omit [IsDomain K] in
instance rightPart_truncatedInclusion_quasiIso :
    QuasiIso (CochainComplex.truncGEMap (rightPartInclusion K D j) 1) := by
  apply (CochainComplex.quasiIso_truncGEMap_iff (rightPartInclusion K D j) 1).mpr
  intro n hn
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = (m + 1 : ℕ) := by
    exact ⟨(n - 1).toNat, by omega⟩
  subst n
  exact rightPartInclusion_quasiIsoAt K D j m

theorem model_isGE_one (hj : 1 ≤ j) : (model K D j).IsGE 1 := by
  rw [CochainComplex.isGE_iff]
  intro n hn
  exact (model K D j).exactAt_of_isGE j n (by omega)

/-- The actual dualized tail, after positive truncation, represents the
full toric model. This is an isomorphism in the native derived category. -/
def nativeTailModelIso (a : ℕ) (h : a + j = D) (hj : 1 ≤ j) :
    Profile.ofResolution (conjugateTailResolution K D a)
      (ModuleCat.of (Laurent K D) (Laurent K D)) ≅ DerivedCategory.Q.obj (model K D j) := by
  let : (model K D j).IsGE 1 := model_isGE_one K D j hj
  exact DerivedCategory.Q.mapIso
    (((ComplexShape.embeddingUpIntGE 1).truncGEFunctor (ModuleCat (Laurent K D))).mapIso
      ((ComplexShape.embeddingUpNat.extendFunctor (ModuleCat (Laurent K D))).mapIso
        (tailModelIso K D a j h).symm)) ≪≫
    asIso (DerivedCategory.Q.map (CochainComplex.truncGEMap (rightPartInclusion K D j) 1)) ≪≫
    (asIso (DerivedCategory.Q.map ((model K D j).πTruncGE 1))).symm

/-- The paper's native profile of the actual matrix-defined toric code,
not a chosen model-profile substitute, is the single coefficient layer. -/
def checks_nativeProfileIso (k a : ℕ) (h : a + (k + 1) = D) :
    Profile.S_X (checks K D k) ≅
      (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) (k + 1 : ℕ)).obj
        (Koszul.coefficientModule K D) := by
  refine (nativeProfileIso K h).symm ≪≫ ?_
  change Profile.ofResolution (conjugateTailResolution K D a)
    (ModuleCat.of (Laurent K D) (Laurent K D)) ≅ _
  exact nativeTailModelIso K D (k + 1) a h (by omega) ≪≫ derivedIso K D (k + 1 : ℕ)

/-- Equivalent native-shift formulation: the shift convention is mathlib's
standard signed cochain convention. -/
def checks_nativeProfileShiftIso (k a : ℕ) (h : a + (k + 1) = D) :
    Profile.S_X (checks K D k) ≅
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) 0).obj
        (Koszul.coefficientModule K D))⟦-((k + 1 : ℕ) : ℤ)⟧ :=
  checks_nativeProfileIso K D k a h ≪≫
    ((DerivedCategory.singleFunctors (ModuleCat (Laurent K D))).shiftIso
      (-((k + 1 : ℕ) : ℤ)) (k + 1 : ℕ) 0 (by omega)).symm.app (Koszul.coefficientModule K D)

end
end Decoupling.HighDim.Toric
