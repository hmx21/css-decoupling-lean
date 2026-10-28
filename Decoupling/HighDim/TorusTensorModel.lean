import Decoupling.HighDim.TorusWindow

/-!
# Actual logical dimension and tensor-model homology

Source: Appendix B.3. The complex below is genuine extension of scalars
of the already constructed bounded finite free CSS model. Its zero
homology is proved isomorphic to the actual periodic check kernel/image
quotient. It is not defined by the binomial count or by a split profile.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits FiniteResolution
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable {K : Type} [Field K] {D q s r : ℕ}

/-- Genuine tensor extension to the period group algebra, followed by
coefficient-field restriction. -/
abbrev tensorPeriodFunctor (L : AddSubgroup (Translation D)) :
    ModuleCat (Laurent K D) ⥤ ModuleCat K :=
  ModuleCat.extendScalars (periodMap L) ⋙ periodCoefficients L

/-- The actual bounded free model tensored to periodic coefficients. -/
def tensorPeriodComplex (L : AddSubgroup (Translation D)) (c : CSS.Checks K D q s r)
    (hc : c.Topological) : CochainComplex (ModuleCat K) ℤ :=
  ((tensorPeriodFunctor L).mapHomologicalComplex (.up ℤ)).obj (cssComplex c hc)

/-- The middle window of the tensor model is exactly the periodic CSS
window, through explicit free-module coordinate isomorphisms. -/
def tensorPeriodWindowIso (L : AddSubgroup (Translation D))
    (c : CSS.Checks K D q s r) (hc : c.Topological) :
    (tensorPeriodComplex L c hc).sc' (-1) 0 1 ≅ periodicSc L c hc :=
  (periodCoefficients L).mapShortComplex.mapIso
    ((ModuleCat.extendScalars (periodMap L)).mapShortComplex.mapIso (cssWindowIso c hc) ≪≫
      extensionWindowIso L c hc) ≪≫ periodicWindowFieldIso L c hc

/-- Canonical coefficient-linear identification with actual periodic
logical supports. This is the first required derived-tensor bridge. -/
def tensorPeriodHomologyEquiv (L : AddSubgroup (Translation D))
    (c : CSS.Checks K D q s r) (hc : c.Topological) :
    (tensorPeriodComplex L c hc).homology 0 ≃ₗ[K] Logical L c hc :=
  ((tensorPeriodComplex L c hc).homologyIsoSc' (-1) 0 1 (by simp) (by simp)).toLinearEquiv.trans
    (((ShortComplex.homologyFunctor (ModuleCat K)).mapIso
      (tensorPeriodWindowIso L c hc)).toLinearEquiv.trans (periodicHomologyEquiv L c hc))

/-- Logical qudit count agrees with the homology of the genuine tensor
model, without finite-dimensional layer or triviality assumptions. -/
theorem logicalQudits_eq_tensorHomology (L : AddSubgroup (Translation D))
    (c : CSS.Checks K D q s r) (hc : c.Topological) :
    logicalQudits L c hc = Module.finrank K ((tensorPeriodComplex L c hc).homology 0) :=
  (tensorPeriodHomologyEquiv L c hc).finrank_eq.symm

end
end Decoupling.HighDim.Torus
