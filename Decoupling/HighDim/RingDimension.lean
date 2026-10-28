import Decoupling.LaurentGlobalDimension
import Decoupling.SwanInduction
import Mathlib.RingTheory.FiniteType
import Mathlib.GroupTheory.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Ext.HasExt

/-!
# Ring-theoretic foundations in arbitrary dimension

The coefficient ring is the actual translation group algebra
`AddMonoidAlgebra K (Fin D → ℤ)`, not a ring supplied with dimension or
freeness assumptions. This file provides the ring-theoretic input used in
`drafts/appendix.tex:19` (global dimension) and
`drafts/appendix.tex:354–360` (Noetherianity and finite projective freeness).

The projective-dimension bound is proved for all modules, by induction on
`D`, starting with vector spaces over `K`. At each successor step it uses
the already proved Laurent extension sequence and the explicit coordinate
ring equivalence. The finite projective freeness theorem invokes the
already proved Swan induction and its equivalence with native freeness.

The Ext vanishing proved here is only in degrees strictly greater than `D`.
The stronger vanishing for CSS cokernels in degrees at least `D` still
requires the topological condition and is not claimed by this file.
-/

namespace Decoupling.HighDim.RingDimension

open CategoryTheory CategoryTheory.Abelian

noncomputable section

universe u

/-- The actual translation group algebra is Noetherian. The finite
generation of the translation monoid makes it a finite-type algebra over
the coefficient field. -/
instance isNoetherianRing (K : Type u) [Field K] (D : ℕ) :
    IsNoetherianRing (LaurentVariables.Ring K D) :=
  Algebra.FiniteType.isNoetherianRing K (LaurentVariables.Ring K D)

/-- Transport a uniform native projective-dimension bound across an actual
ring equivalence. No dimension assumption on the source ring is added. -/
theorem projectiveDimensionLE_of_ringEquiv {A B : Type u} [CommRing A] [CommRing B]
    (e : A ≃+* B) (n : ℕ)
    (hB : ∀ N : ModuleCat.{u} B, HasProjectiveDimensionLE N n)
    (M : ModuleCat.{u} A) : HasProjectiveDimensionLE M n := by
  let E := ModuleCat.restrictScalarsEquivalenceOfRingEquiv e
  have : HasProjectiveDimensionLE (E.inverse.obj M) n := hB (E.inverse.obj M)
  have hF : HasProjectiveDimensionLE (E.functor.obj (E.inverse.obj M)) n :=
    ScalarExtensionDimension.functor_projectiveDimensionLE E.functor n (E.inverse.obj M)
  exact @hasProjectiveDimensionLT_of_iso _ _ _ _ _ (E.counitIso.app M) (n + 1) hF

/-- Every vector space, without a finite-dimensionality hypothesis, has
native projective dimension at most zero. -/
theorem field_projectiveDimensionLE (K : Type u) [Field K] (M : ModuleCat.{u} K) :
    HasProjectiveDimensionLE M 0 := by
  have : Module.Free K M := inferInstance
  have : Module.Projective K M := inferInstance
  exact (projective_iff_hasProjectiveDimensionLE_zero M).mp inferInstance

/-- The actual `D`-variable Laurent ring over any field has global
projective-dimension bound `D`. The module need not be finitely generated. -/
theorem projectiveDimensionLE (K : Type u) [Field K] (D : ℕ)
    (M : ModuleCat.{u} (LaurentVariables.Ring K D)) : HasProjectiveDimensionLE M D := by
  induction D with
  | zero =>
    exact projectiveDimensionLE_of_ringEquiv (LaurentVariables.zeroEquiv K) 0
      (field_projectiveDimensionLE K) M
  | succ D ih =>
    exact projectiveDimensionLE_of_ringEquiv (LaurentVariables.successorEquiv K D) (D + 1)
      (LaurentGlobalDimension.laurent_bound D ih) M

/-- Finite projective modules over the actual finite-variable Laurent ring
are native free modules. Both finiteness and projectivity are hypotheses
on the module; the ring's Swan theorem is proved, not hypothesized. -/
theorem finite_projective_free (K : Type u) [Field K] (D : ℕ)
    (P : Type u) [AddCommGroup P] [Module (LaurentVariables.Ring K D) P]
    [Module.Finite (LaurentVariables.Ring K D) P]
    [Module.Projective (LaurentVariables.Ring K D) P] :
    Module.Free (LaurentVariables.Ring K D) P :=
  (ProjectiveFreeness.criterion_iff_native.mp (SwanInduction.criterion D K)) P

/-- Genuine derived Ext vanishes strictly above the number of variables,
for arbitrary source and target modules. This is not the sharper CSS
cokernel vanishing at degree `D`. -/
theorem ext_eq_zero_above_dimension (K : Type u) [Field K] (D : ℕ)
    (M N : ModuleCat.{u} (LaurentVariables.Ring K D))
    {j : ℕ} (hj : D < j) (e : Ext M N j) : e = 0 := by
  have : HasProjectiveDimensionLE M D := projectiveDimensionLE K D M
  exact e.eq_zero_of_hasProjectiveDimensionLT (D + 1) hj

end

end Decoupling.HighDim.RingDimension
