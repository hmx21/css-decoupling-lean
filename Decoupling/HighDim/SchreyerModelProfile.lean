import Decoupling.HighDim.SchreyerModel
import Decoupling.HighDim.ResolutionComparison

/-!
# HD014 full native profile of the Schreyer connected model

The comparison uses an actual map of complexes and native derived
localization after positive truncation. It retains all extension data,
not merely the individual Ext groups. The tail input is an intermediate
consumer interface, discharged by the separate existence construction.
-/
namespace Decoupling.HighDim.SchreyerCSS
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
variable {K : Type} [Field K] {D q s r : ℕ}

def nonnegativeInclusion (c : CSS.Checks K D q s r) (A : Input c) (hc : c.Topological) :
    Profile.rHomComplex (conjugateResolution c A)
      (ModuleCat.of (Laurent K D) (Laurent K D)) ⟶ complex c A hc where
  f
    | .ofNat n => ((dual c A).extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom
    | .negSucc _ => 0
  comm' i j hij := by
    change i + 1 = j at hij
    subst j
    cases i with
    | ofNat n =>
      change ((dual c A).extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom ≫
          (dual c A).d n (n + 1) =
        ((dual c A).extend ComplexShape.embeddingUpNat).d (n : ℤ) (n + 1 : ℕ) ≫
          ((dual c A).extendXIso ComplexShape.embeddingUpNat (i := n + 1) rfl).hom
      rw [(dual c A).extend_d_eq ComplexShape.embeddingUpNat
        (i := n) (j := n + 1) (i' := (n : ℤ)) (j' := ((n + 1 : ℕ) : ℤ)) rfl rfl]
      simp
    | negSucc n =>
      exact ((dual c A).isZero_extend_X ComplexShape.embeddingUpNat (Int.negSucc n)
        (by intro k; simp)).eq_of_src _ _

instance nonnegativeInclusion_isIso (c : CSS.Checks K D q s r) (A : Input c)
    (hc : c.Topological) (n : ℕ) : IsIso ((nonnegativeInclusion c A hc).f n) := by
  change IsIso ((dual c A).extendXIso ComplexShape.embeddingUpNat (i := n) rfl).hom
  infer_instance

theorem nonnegativeInclusion_quasiIsoAt (c : CSS.Checks K D q s r) (A : Input c)
    (hc : c.Topological) (n : ℕ) : QuasiIsoAt (nonnegativeInclusion c A hc) (n + 1 : ℕ) := by
  rw [quasiIsoAt_iff' (nonnegativeInclusion c A hc) (n : ℤ)
    (n + 1 : ℕ) (n + 2 : ℕ) (by simp) (by simp; omega)]
  let f := (shortComplexFunctor' (ModuleCat (Laurent K D)) (ComplexShape.up ℤ)
      (n : ℕ) (n + 1 : ℕ) (n + 2 : ℕ)).map (nonnegativeInclusion c A hc)
  let : IsIso f.τ₁ := nonnegativeInclusion_isIso c A hc n
  let : IsIso f.τ₂ := nonnegativeInclusion_isIso c A hc (n + 1)
  let : IsIso f.τ₃ := nonnegativeInclusion_isIso c A hc (n + 2)
  let : IsIso f := ShortComplex.isIso_of_isIso f
  change ShortComplex.QuasiIso f
  infer_instance

def truncatedInclusion (c : CSS.Checks K D q s r) (A : Input c) (hc : c.Topological) :
    Profile.positiveComplex (conjugateResolution c A)
      (ModuleCat.of (Laurent K D) (Laurent K D)) ⟶ (complex c A hc).truncGE 1 :=
  CochainComplex.truncGEMap (nonnegativeInclusion c A hc) 1

instance truncatedInclusion_quasiIso (c : CSS.Checks K D q s r) (A : Input c) (hc : c.Topological) :
    QuasiIso (truncatedInclusion c A hc) := by
  apply (CochainComplex.quasiIso_truncGEMap_iff (nonnegativeInclusion c A hc) 1).mpr
  intro n hn
  obtain ⟨m, hm⟩ : ∃ m : ℕ, n = (m + 1 : ℕ) := by
    exact ⟨(n - 1).toNat, by omega⟩
  subst n
  exact nonnegativeInclusion_quasiIsoAt c A hc m

/-- The constructed full finite free complex represents the exact native
positive RHom profile, not just its individual cohomology groups. -/
def complex_profileIso (c : CSS.Checks K D q s r) (A : Input c) (hc : c.Topological) :
    DerivedCategory.Q.obj (complex c A hc) ≅ Profile.S_X c :=
  asIso (DerivedCategory.Q.map ((complex c A hc).πTruncGE 1)) ≪≫
    (asIso (DerivedCategory.Q.map (truncatedInclusion c A hc))).symm ≪≫
    ResolutionComparison.profileIso (ModuleCat.of (Laurent K D) (Laurent K D))
      (conjugateResolution c A) (Profile.resolution c)


end
end Decoupling.HighDim.SchreyerCSS
