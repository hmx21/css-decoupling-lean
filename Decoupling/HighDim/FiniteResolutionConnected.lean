import Decoupling.HighDim.FiniteResolutionDual
import Mathlib.Algebra.Homology.Embedding.Connect
import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-!
# A genuine bounded finite free cochain model with the physical window

Source: appendix C1. A finite free resolution of the actual image of
`H_Z†` supplies the negative degrees; the actual conjugate-dual resolution
supplies the nonnegative degrees. The two are joined by `H_Z†`, using
the proved coordinate identification in degree zero. Topology is used
for the connecting square and exactness in degree zero.
-/

namespace Decoupling.HighDim.FiniteResolution

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Matrix

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {K : Type} [Field K] {D q s r : ℕ}

def zImage (c : CSS.Checks K D q s r) : ModuleCat (Laurent K D) :=
  ModuleCat.of (Laurent K D) (LinearMap.range (dagger c.H_Z).mulVecLin)

def zCover (c : CSS.Checks K D q s r) :
    ModuleCat.of (Laurent K D) (CSS.Free K D r) ⟶ zImage c :=
  ModuleCat.ofHom (dagger c.H_Z).mulVecLin.rangeRestrict

theorem zCover_surjective (c : CSS.Checks K D q s r) :
    Function.Surjective (zCover c).hom :=
  LinearMap.surjective_rangeRestrict _

/-- The degree-minus-one term remains the original Z-check module. -/
def zData (c : CSS.Checks K D q s r) : Data (zImage c) (D + 1) := by
  letI : Module.Finite (Laurent K D) (Laurent K D) := Module.Finite.self _
  letI : Module.Finite (Laurent K D)
      (ModuleCat.of (Laurent K D) (CSS.Free K D r)) := by
    change Module.Finite (Laurent K D) (Fin r → Laurent K D)
    exact Module.Finite.pi
  exact prepend (zCover c) (zCover_surjective c) (laurent (Syzygy (zCover c)))

def connectingMap (c : CSS.Checks K D q s r) :
    (zData c).complex.X 0 ⟶ (cssDual c).X 0 :=
  ModuleCat.ofHom ((cssDualZeroCoordinates c).symm.toLinearMap.comp
    (dagger c.H_Z).mulVecLin)

@[simp] theorem connectingMap_coordinates (c : CSS.Checks K D q s r)
    (v : CSS.Free K D r) :
    cssDualZeroCoordinates c (connectingMap c v) = dagger c.H_Z *ᵥ v :=
  (cssDualZeroCoordinates c).apply_symm_apply _

def connection (c : CSS.Checks K D q s r) (hc : c.Topological) :
    CochainComplex.ConnectData (zData c).complex (cssDual c) where
  d₀ := connectingMap c
  comp_d₀ := by
    ext x
    apply (cssDualZeroCoordinates c).injective
    change cssDualZeroCoordinates c (connectingMap c ((zData c).complex.d 1 0 x)) =
      cssDualZeroCoordinates c 0
    rw [map_zero, connectingMap_coordinates, (zData c).complex_d 0]
    exact congrArg (fun f => (f x : zImage c).val) (zData c).d_ε
  d₀_comp := by
    ext x
    apply (cssDualOneCoordinates c).injective
    change cssDualOneCoordinates c ((cssDual c).d 0 1 (connectingMap c x)) =
      cssDualOneCoordinates c 0
    rw [map_zero, cssDual_d_zero_one, connectingMap_coordinates]
    exact (c.exact_X hc _).mpr ⟨x, rfl⟩

/-- The actual integer-indexed finite free model, with qudits in degree zero. -/
def cssComplex (c : CSS.Checks K D q s r) (hc : c.Topological) :
    CochainComplex (ModuleCat (Laurent K D)) ℤ :=
  (connection c hc).cochainComplex

@[simp] theorem cssComplex_X_nonneg (c : CSS.Checks K D q s r) (hc : c.Topological)
    (n : ℕ) : (cssComplex c hc).X n = (cssDual c).X n := rfl

@[simp] theorem cssComplex_X_negSucc (c : CSS.Checks K D q s r) (hc : c.Topological)
    (n : ℕ) : (cssComplex c hc).X (Int.negSucc n) = (zData c).X n := rfl

@[simp] theorem cssComplex_d_zero_one (c : CSS.Checks K D q s r) (hc : c.Topological) :
    (cssComplex c hc).d 0 1 = (cssDual c).d 0 1 := rfl

@[simp] theorem cssComplex_d_minus_one_zero (c : CSS.Checks K D q s r)
    (hc : c.Topological) : (cssComplex c hc).d (-1) 0 = connectingMap c := rfl

instance cssComplex_finite (c : CSS.Checks K D q s r) (hc : c.Topological) (n : ℤ) :
    Module.Finite (Laurent K D) ((cssComplex c hc).X n) := by
  cases n with
  | ofNat n => exact cssDual_finite c n
  | negSucc n => exact (zData c).finite n

instance cssComplex_free (c : CSS.Checks K D q s r) (hc : c.Topological) (n : ℤ) :
    Module.Free (Laurent K D) ((cssComplex c hc).X n) := by
  cases n with
  | ofNat n => exact cssDual_free c n
  | negSucc n => exact (zData c).free n

instance cssComplex_projective (c : CSS.Checks K D q s r) (hc : c.Topological) (n : ℤ) :
    Projective ((cssComplex c hc).X n) := inferInstance

instance cssComplex_boundedAbove (c : CSS.Checks K D q s r) (hc : c.Topological) :
    (cssComplex c hc).IsStrictlyLE (D + 2) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  cases n with
  | ofNat n => exact cssDual_zero_above c n (by simp only [Int.ofNat_eq_natCast] at hn; omega)
  | negSucc n => omega

instance cssComplex_boundedBelow (c : CSS.Checks K D q s r) (hc : c.Topological) :
    (cssComplex c hc).IsStrictlyGE (-(D + 2 : ℕ)) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  cases n with
  | ofNat n => simp only [Int.ofNat_eq_natCast] at hn; omega
  | negSucc n => exact (zData c).zero_above n (by omega)

theorem cssComplex_exact_zero (c : CSS.Checks K D q s r) (hc : c.Topological) :
    (cssComplex c hc).ExactAt 0 := by
  rw [(cssComplex c hc).exactAt_iff' (-1) 0 1 (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  have hx' : c.H_X *ᵥ cssDualZeroCoordinates c x = 0 := by
    rw [← cssDual_d_zero_one]
    exact congrArg (cssDualOneCoordinates c) hx
  obtain ⟨z, hz⟩ := (c.exact_X hc _).mp hx'
  refine ⟨z, ?_⟩
  apply (cssDualZeroCoordinates c).injective
  change cssDualZeroCoordinates c (connectingMap c z) = _
  rw [connectingMap_coordinates]
  exact hz

theorem cssComplex_exact_minus_one (c : CSS.Checks K D q s r)
    (hc : c.Topological) : (cssComplex c hc).ExactAt (-1) := by
  rw [(cssComplex c hc).exactAt_iff' (-2) (-1) 0 (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  have hx' : (zData c).ε x = 0 := by
    apply Subtype.ext
    have hh := congrArg (cssDualZeroCoordinates c) hx
    change cssDualZeroCoordinates c (connectingMap c x) = cssDualZeroCoordinates c 0 at hh
    rw [connectingMap_coordinates, map_zero] at hh
    exact hh
  have hxmem : x ∈ LinearMap.range ((zData c).d 0).hom := by
    rw [(zData c).exact_zero]
    exact hx'
  exact hxmem

theorem cssComplex_exact_negative (c : CSS.Checks K D q s r)
    (hc : c.Topological) (n : ℕ) : (cssComplex c hc).ExactAt (Int.negSucc (n + 1)) := by
  rw [(cssComplex c hc).exactAt_iff' (Int.negSucc (n + 2))
    (Int.negSucc (n + 1)) (Int.negSucc n) (by simp) (by simp; omega)]
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    cssComplex, CochainComplex.ConnectData.cochainComplex_d,
    CochainComplex.ConnectData.d_negSucc, Data.complex_d] using (zData c).exact_succ n

instance cssComplex_isGE (c : CSS.Checks K D q s r) (hc : c.Topological) :
    (cssComplex c hc).IsGE 1 := by
  rw [CochainComplex.isGE_iff]
  intro n hn
  cases n with
  | ofNat n =>
    have : n = 0 := by simp only [Int.ofNat_eq_natCast] at hn; omega
    subst this
    exact cssComplex_exact_zero c hc
  | negSucc n =>
    cases n with
    | zero => exact cssComplex_exact_minus_one c hc
    | succ n => exact cssComplex_exact_negative c hc n

/-- Positive homology of the connected model is the actual native Ext. -/
def cssComplex_positiveHomologyEquivExt (c : CSS.Checks K D q s r)
    (hc : c.Topological) (n : ℕ) :
    (cssComplex c hc).homology (n + 1 : ℕ) ≃ₗ[Laurent K D] Layers.E_X c (n + 1) :=
  ((connection c hc).homologyIsoPos (n + 1) (n + 1 : ℕ) rfl).toLinearEquiv.trans
    (ResolutionCohomology.homologyEquivExt (cssConjugateResolution c)
      (ModuleCat.of (Laurent K D) (Laurent K D)) n)

end
end Decoupling.HighDim.FiniteResolution
