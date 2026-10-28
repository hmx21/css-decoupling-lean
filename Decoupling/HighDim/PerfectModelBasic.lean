import Decoupling.HighDim.TorusTensorMaps
import Decoupling.HighDim.FiniteResolutionLaurent

/-!
# Bounded finite-free models of actual Laurent modules and their shifts

All resolutions are constructed from the proved Laurent Noetherianity,
finite projective-dimension bound, and finite-projective freeness.
-/
namespace Decoupling.HighDim.PerfectModel
open CategoryTheory CategoryTheory.Limits Torus
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] {D : ℕ}

def ofIso {X Y : Derived K D} (M : TensorModel X) (e : X ≅ Y) : TensorModel Y :=
  { M with iso := M.iso ≪≫ e }

def shift {X : Derived K D} (M : TensorModel X) (a : ℤ) : TensorModel (X⟦a⟧) where
  complex := M.complex⟦a⟧
  lower := M.lower - a
  upper := M.upper - a
  finite n := by change Module.Finite (Laurent K D) (M.complex.X (n + a)); infer_instance
  free n := by change Module.Free (Laurent K D) (M.complex.X (n + a)); infer_instance
  boundedBelow := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    exact M.complex.isZero_of_isStrictlyGE M.lower (n + a) (by omega)
  boundedAbove := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact M.complex.isZero_of_isStrictlyLE M.upper (n + a) (by omega)
  iso := (DerivedCategory.Q.commShiftIso a).app M.complex ≪≫
    (shiftFunctor (Derived K D) a).mapIso M.iso

theorem singleZero_exists (A : ModuleCat (Laurent K D)) [Module.Finite (Laurent K D) A] :
    Nonempty (TensorModel ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) 0).obj A)) := by
  obtain ⟨P, hfin, hfree, hzero⟩ := FiniteResolution.exists_native_free A
  have finite (n : ℤ) : Module.Finite (Laurent K D) (P.cochainComplex.X n) := by
    by_cases hn : n ≤ 0
    · let := hfin (-n).toNat
      exact Module.Finite.equiv (P.cochainComplexXIso n (-n).toNat (by omega)).symm.toLinearEquiv
    · let := ModuleCat.subsingleton_of_isZero (P.cochainComplex.isZero_of_isStrictlyLE 0 n (by omega))
      infer_instance
  have free (n : ℤ) : Module.Free (Laurent K D) (P.cochainComplex.X n) := by
    by_cases hn : n ≤ 0
    · let := hfree (-n).toNat
      exact Module.Free.of_equiv (P.cochainComplexXIso n (-n).toNat (by omega)).symm.toLinearEquiv
    · let := ModuleCat.subsingleton_of_isZero (P.cochainComplex.isZero_of_isStrictlyLE 0 n (by omega))
      infer_instance
  refine ⟨{
    complex := P.cochainComplex
    lower := -(D : ℤ)
    upper := 0
    finite := finite
    free := free
    boundedBelow := ?_
    boundedAbove := inferInstance
    iso := asIso (DerivedCategory.Q.map P.π') ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat (Laurent K D)) 0).app A).symm }⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  exact (hzero (-n).toNat (by omega)).of_iso (P.cochainComplexXIso n (-n).toNat (by omega))

/-- Every finitely generated actual Laurent module in any degree has a
bounded finite-free model. -/
theorem single_exists (A : ModuleCat (Laurent K D)) [Module.Finite (Laurent K D) A] (j : ℤ) :
    Nonempty (TensorModel ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj A)) := by
  obtain ⟨M⟩ := singleZero_exists A
  exact ⟨ofIso (shift M (-j))
    (((DerivedCategory.singleFunctors (ModuleCat (Laurent K D))).shiftIso (-j) j 0 (by omega)).app A)⟩

end
end Decoupling.HighDim.PerfectModel
