import Decoupling.HighDim.ResolutionCohomology
import Decoupling.HighDim.DegreeBound
import Mathlib.Algebra.Homology.DerivedCategory.TStructure

/-!
# The actual positive derived Hom profile

Source: `drafts/main.tex`, the definition `S_X = τ≥1 RHom(bar M_X,R)`.
We form Hom of an actual projective resolution, extend its nonnegative
cochain degrees to integers, apply the canonical good truncation, and
localize in mathlib's derived category. This construction retains the
differentials and extension data; it is not the direct sum of Ext layers.

`homologyEquivLayer` identifies its positive cohomology with the actual
native Ext groups. Independence of the chosen resolution and restriction
compatibility will be proved using comparison maps separately.
-/

namespace Decoupling.HighDim.Profile

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
open ResolutionCohomology

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {R : Type} [CommRing R] {X : ModuleCat R}
  (P : ProjectiveResolution X) (Y : ModuleCat R)

/-- The actual dual projective-resolution complex, extended by zero to ℤ. -/
def rHomComplex : CochainComplex (ModuleCat R) ℤ :=
  (dualComplex P Y).extend ComplexShape.embeddingUpNat

/-- Canonical good truncation; its degree-one term is an opcycles quotient. -/
def positiveComplex : CochainComplex (ModuleCat R) ℤ :=
  (rHomComplex P Y).truncGE 1

/-- An object of the genuine derived category, retaining all gluing data. -/
def ofResolution : DerivedCategory (ModuleCat R) :=
  DerivedCategory.Q.obj (positiveComplex P Y)

instance positiveComplex_isStrictlyGE : (positiveComplex P Y).IsStrictlyGE 1 := by
  dsimp [positiveComplex]
  infer_instance

instance ofResolution_isGE : (ofResolution P Y).IsGE 1 := by
  dsimp [ofResolution]
  infer_instance

def rHomHomologyEquivExt (n : ℕ) :
    (rHomComplex P Y).homology (n + 1 : ℕ) ≃ₗ[R]
      CategoryTheory.Abelian.Ext X Y (n + 1) :=
  ((dualComplex P Y).extendHomologyIso ComplexShape.embeddingUpNat
    (j := n + 1) rfl).toLinearEquiv.trans (homologyEquivExt P Y n)

def positiveHomologyEquivExt (n : ℕ) :
    (positiveComplex P Y).homology (n + 1 : ℕ) ≃ₗ[R]
      CategoryTheory.Abelian.Ext X Y (n + 1) := by
  letI : QuasiIsoAt ((rHomComplex P Y).πTruncGE 1) (n + 1 : ℕ) :=
    (rHomComplex P Y).quasiIsoAt_πTruncGE 1 _ (by omega)
  exact (asIso (HomologicalComplex.homologyMap
    ((rHomComplex P Y).πTruncGE 1) (n + 1 : ℕ))).symm.toLinearEquiv.trans
      (rHomHomologyEquivExt P Y n)

def derivedHomologyEquivExt (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat R) (n + 1 : ℕ)).obj
      (ofResolution P Y) ≃ₗ[R] CategoryTheory.Abelian.Ext X Y (n + 1) :=
  ((DerivedCategory.homologyFunctorFactors (ModuleCat R) (n + 1 : ℕ)).app
    (positiveComplex P Y)).toLinearEquiv.trans (positiveHomologyEquivExt P Y n)

variable {K : Type} [CommRing K] {D q s r : ℕ}

/-- A chosen genuine projective resolution of the conjugated reduced module. -/
def resolution (c : CSS.Checks K D q s r) :
    ProjectiveResolution (Layers.conjugate (Layers.reduced c)) :=
  projectiveResolution (Layers.conjugate (Layers.reduced c))

/-- The paper's X-sector profile, using a genuine projective-resolution model. -/
def S_X (c : CSS.Checks K D q s r) : DerivedCategory (ModuleCat (Laurent K D)) :=
  ofResolution (resolution c) (ModuleCat.of (Laurent K D) (Laurent K D))

def S_Z (c : CSS.Checks K D q s r) := S_X c.swap

instance S_X_isGE (c : CSS.Checks K D q s r) : (S_X c).IsGE 1 :=
  ofResolution_isGE _ _

/-- Positive cohomology is the exact Ext used in the hypotheses. -/
def homologyEquivLayer (c : CSS.Checks K D q s r) (n : ℕ) :
    (DerivedCategory.homologyFunctor (ModuleCat (Laurent K D)) (n + 1 : ℕ)).obj
      (S_X c) ≃ₗ[Laurent K D] Layers.E_X c (n + 1) :=
  derivedHomologyEquivExt (resolution c) _ n

end
end Decoupling.HighDim.Profile
