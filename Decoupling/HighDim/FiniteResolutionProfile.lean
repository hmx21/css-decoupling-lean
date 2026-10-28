import Decoupling.HighDim.FiniteResolutionConnected
import Decoupling.HighDim.ResolutionComparison

/-!
# The bounded finite free CSS model represents the actual profile

The map below includes the actual nonnegative dual resolution into the
connected physical-window model. It is an isomorphism on every
nonnegative term, hence a quasi-isomorphism in positive degrees. Applying
good truncation and the derived localization gives an actual derived
isomorphism, retaining all extension data.
-/

namespace Decoupling.HighDim.FiniteResolution

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex

noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] {D q s r : ℕ}

def nonnegativeInclusion (c : CSS.Checks K D q s r) (hc : c.Topological) :
    Profile.rHomComplex (cssConjugateResolution c)
      (ModuleCat.of (Laurent K D) (Laurent K D)) ⟶ cssComplex c hc where
  f
    | .ofNat n => ((cssDual c).extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom
    | .negSucc _ => 0
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    cases i with
    | ofNat n =>
      change ((cssDual c).extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom ≫
          (cssDual c).d n (n + 1) =
        ((cssDual c).extend ComplexShape.embeddingUpNat).d (n : ℤ) (n + 1 : ℕ) ≫
          ((cssDual c).extendXIso ComplexShape.embeddingUpNat (i := n + 1) rfl).hom
      rw [(cssDual c).extend_d_eq ComplexShape.embeddingUpNat
        (i := n) (j := n + 1) (i' := (n : ℤ)) (j' := ((n + 1 : ℕ) : ℤ)) rfl rfl]
      simp
    | negSucc n =>
      exact ((cssDual c).isZero_extend_X ComplexShape.embeddingUpNat (Int.negSucc n)
        (by intro k; simp)).eq_of_src _ _

instance nonnegativeInclusion_isIso (c : CSS.Checks K D q s r)
    (hc : c.Topological) (n : ℕ) : IsIso ((nonnegativeInclusion c hc).f n) := by
  change IsIso ((cssDual c).extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom
  infer_instance

theorem nonnegativeInclusion_quasiIsoAt (c : CSS.Checks K D q s r)
    (hc : c.Topological) (n : ℕ) : QuasiIsoAt (nonnegativeInclusion c hc) (n + 1 : ℕ) := by
  rw [quasiIsoAt_iff' (nonnegativeInclusion c hc) (n : ℤ)
    (n + 1 : ℕ) (n + 2 : ℕ) (by simp) (by simp; omega)]
  let f := (shortComplexFunctor' (ModuleCat (Laurent K D)) (ComplexShape.up ℤ)
      (n : ℕ) (n + 1 : ℕ) (n + 2 : ℕ)).map (nonnegativeInclusion c hc)
  let : IsIso f.τ₁ := nonnegativeInclusion_isIso c hc n
  let : IsIso f.τ₂ := nonnegativeInclusion_isIso c hc (n + 1)
  let : IsIso f.τ₃ := nonnegativeInclusion_isIso c hc (n + 2)
  let : IsIso f := ShortComplex.isIso_of_isIso f
  change ShortComplex.QuasiIso f
  infer_instance

def truncatedInclusion (c : CSS.Checks K D q s r) (hc : c.Topological) :
    Profile.positiveComplex (cssConjugateResolution c)
      (ModuleCat.of (Laurent K D) (Laurent K D)) ⟶ (cssComplex c hc).truncGE 1 :=
  CochainComplex.truncGEMap (nonnegativeInclusion c hc) 1

instance truncatedInclusion_quasiIso (c : CSS.Checks K D q s r) (hc : c.Topological) :
    QuasiIso (truncatedInclusion c hc) := by
  apply (CochainComplex.quasiIso_truncGEMap_iff (nonnegativeInclusion c hc) 1).mpr
  intro n hn
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = (m + 1 : ℕ) := by
    exact ⟨(n - 1).toNat, by omega⟩
  subst n
  exact nonnegativeInclusion_quasiIsoAt c hc m

/-- The constructed full finite free complex represents the exact native
positive RHom profile, not just its individual cohomology groups. -/
def cssComplex_profileIso (c : CSS.Checks K D q s r) (hc : c.Topological) :
    DerivedCategory.Q.obj (cssComplex c hc) ≅ Profile.S_X c :=
  asIso (DerivedCategory.Q.map ((cssComplex c hc).πTruncGE 1)) ≪≫
    (asIso (DerivedCategory.Q.map (truncatedInclusion c hc))).symm ≪≫
    ResolutionComparison.profileIso (ModuleCat.of (Laurent K D) (Laurent K D))
      (cssConjugateResolution c) (Profile.resolution c)

end
end Decoupling.HighDim.FiniteResolution
