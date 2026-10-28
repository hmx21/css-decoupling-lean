import Decoupling.HighDim.FiniteResolutionPresentation
import Decoupling.HighDim.ResolutionCohomology
import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix

/-!
# Finite free native resolutions for CSS reduced modules

The given `H_X† : Rˢ → Rᑫ` is retained as the first differential of an
actual finite free resolution of `M_X`. Conjugating that entire native
resolution yields a finite free resolution of the genuine `bar M_X`.
These are ready inputs to the native dual/profile construction; the
two-sided physical-window model is not redefined as a profile here.
-/

namespace Decoupling.HighDim.FiniteResolution

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

noncomputable section
variable {K : Type} [Field K] {D q s r : ℕ}

/-- The identity of underlying abelian groups, as a semilinear map into
the actual antipode-twisted module. -/
def toConjugate (M : ModuleCat (Laurent K D)) :
    M →ₛₗ[(bar : Laurent K D ≃+* Laurent K D).toRingHom] Layers.conjugate M where
  toFun x := x
  map_add' _ _ := rfl
  map_smul' a x := by
    change a • x = bar (bar a) • x
    rw [bar_bar]

theorem conjugate_finite (M : ModuleCat (Laurent K D))
    [Module.Finite (Laurent K D) M] :
    Module.Finite (Laurent K D) (Layers.conjugate M) :=
  Module.Finite.of_surjective (toConjugate M) (fun x => ⟨x, rfl⟩)

/-- The given X-stabilizer map, with unchanged finite coordinate modules. -/
def cssPresentation (c : CSS.Checks K D q s r) :
    ModuleCat.of (Laurent K D) (CSS.Free K D s) ⟶
      ModuleCat.of (Laurent K D) (CSS.Free K D q) :=
  ModuleCat.ofHom (dagger c.H_X).mulVecLin

instance cssReduced_finite (c : CSS.Checks K D q s r) :
    Module.Finite (Laurent K D) (Layers.reduced c) := by
  change Module.Finite (Laurent K D) c.M_X
  infer_instance

/-- Actual bounded finite projective data retaining the supplied checks. -/
def cssData (c : CSS.Checks K D q s r) : Data (Layers.reduced c) (D + 2) :=
  presentationData (cssPresentation c)

/-- The corresponding native resolution of the actual reduced module. -/
def cssResolution (c : CSS.Checks K D q s r) : ProjectiveResolution (Layers.reduced c) :=
  (cssData c).toProjectiveResolution

@[simp] theorem cssResolution_d_one_zero (c : CSS.Checks K D q s r) :
    (cssResolution c).complex.d 1 0 = cssPresentation c :=
  presentationResolution_d_one_zero (cssPresentation c)

instance cssResolution_finite (c : CSS.Checks K D q s r) (k : ℕ) :
    Module.Finite (Laurent K D) ((cssResolution c).complex.X k) := (cssData c).finite k

instance cssResolution_free (c : CSS.Checks K D q s r) (k : ℕ) :
    Module.Free (Laurent K D) ((cssResolution c).complex.X k) := (cssData c).free k

/-- Conjugate the actual resolution, preserving exactness and projectivity
through the ring automorphism's equivalence of module categories. -/
def cssConjugateResolution (c : CSS.Checks K D q s r) :
    ProjectiveResolution (Layers.conjugate (Layers.reduced c)) :=
  (ModuleCat.restrictScalars (bar : Laurent K D ≃+* Laurent K D).toRingHom).mapProjectiveResolution
    (cssResolution c)

instance cssConjugateResolution_finite (c : CSS.Checks K D q s r) (k : ℕ) :
    Module.Finite (Laurent K D) ((cssConjugateResolution c).complex.X k) :=
  conjugate_finite ((cssResolution c).complex.X k)

instance cssConjugateResolution_free (c : CSS.Checks K D q s r) (k : ℕ) :
    Module.Free (Laurent K D) ((cssConjugateResolution c).complex.X k) :=
  RingDimension.finite_projective_free K D ((cssConjugateResolution c).complex.X k)

theorem cssConjugateResolution_zero_above (c : CSS.Checks K D q s r)
    (k : ℕ) (hk : D + 2 < k) : IsZero ((cssConjugateResolution c).complex.X k) :=
  (ModuleCat.restrictScalars (bar : Laurent K D ≃+* Laurent K D).toRingHom).map_isZero
    ((cssData c).zero_above k hk)

/-- With topology, one may separately choose a shorter resolution using
the proved bound `pd(bar M_X) ≤ D-1`. This choice does not retain the
prescribed first checks; use `cssConjugateResolution` when they matter. -/
def cssShortConjugateData (c : CSS.Checks K D q s r) (hc : c.Topological)
    (hD : 1 ≤ D) : Data (Layers.conjugate (Layers.reduced c)) (D - 1) := by
  letI := conjugate_finite (Layers.reduced c)
  letI := DegreeBound.conjugate_projectiveDimensionLE c hc hD
  exact ofDimensionBound (D - 1) (Layers.conjugate (Layers.reduced c))

/-- The actual nonnegative Hom complex of the finite conjugated resolution. -/
def cssDual (c : CSS.Checks K D q s r) : CochainComplex (ModuleCat (Laurent K D)) ℕ :=
  ResolutionCohomology.dualComplex (cssConjugateResolution c)
    (ModuleCat.of (Laurent K D) (Laurent K D))

instance cssDual_finite (c : CSS.Checks K D q s r) (k : ℕ) :
    Module.Finite (Laurent K D) ((cssDual c).X k) := by
  change Module.Finite (Laurent K D)
    ((cssConjugateResolution c).complex.X k ⟶ ModuleCat.of (Laurent K D) (Laurent K D))
  exact Module.Finite.equiv ModuleCat.homLinearEquiv.symm

instance cssDual_free (c : CSS.Checks K D q s r) (k : ℕ) :
    Module.Free (Laurent K D) ((cssDual c).X k) := by
  change Module.Free (Laurent K D)
    ((cssConjugateResolution c).complex.X k ⟶ ModuleCat.of (Laurent K D) (Laurent K D))
  exact Module.Free.of_equiv ModuleCat.homLinearEquiv.symm

theorem cssDual_zero_above (c : CSS.Checks K D q s r) (k : ℕ) (hk : D + 2 < k) :
    IsZero ((cssDual c).X k) := by
  let : Subsingleton
      ((cssConjugateResolution c).complex.X k ⟶ ModuleCat.of (Laurent K D) (Laurent K D)) :=
    ⟨fun f g => (cssConjugateResolution_zero_above c k hk).eq_of_src f g⟩
  change IsZero (ModuleCat.of (Laurent K D)
    ((cssConjugateResolution c).complex.X k ⟶ ModuleCat.of (Laurent K D) (Laurent K D)))
  exact ModuleCat.isZero_of_subsingleton _

end

end Decoupling.HighDim.FiniteResolution
