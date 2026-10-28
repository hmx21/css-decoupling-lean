import Decoupling.HighDim.SchreyerCSS

/-!
# HD014 connected native model from the actual Schreyer-tail consumer

The complex keeps the physical H_Z†, H_X, and gamma window. This file
proves actual exactness, finite-power freeness, boundedness, and native Ext
identification. Input tail existence is discharged separately.
-/
namespace Decoupling.HighDim.SchreyerCSS
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
variable {K : Type} [Field K] {D q s r : ℕ}

def connectingMap (c : CSS.Checks K D q s r) (A : Input c) :
    ((zFreeData c A).data).complex.X 0 ⟶ (dual c A).X 0 :=
  ModuleCat.ofHom ((zeroCoordinates c A).symm.toLinearMap.comp
    (dagger c.H_Z).mulVecLin)

@[simp] theorem connectingMap_coordinates (c : CSS.Checks K D q s r) (A : Input c)
    (v : CSS.Free K D r) :
    zeroCoordinates c A (connectingMap c A v) = dagger c.H_Z *ᵥ v :=
  (zeroCoordinates c A).apply_symm_apply _

def connection (c : CSS.Checks K D q s r) (A : Input c) (hc : c.Topological) :
    CochainComplex.ConnectData ((zFreeData c A).data).complex (dual c A) where
  d₀ := connectingMap c A
  comp_d₀ := by
    ext x
    apply (zeroCoordinates c A).injective
    change zeroCoordinates c A (connectingMap c A (((zFreeData c A).data).complex.d 1 0 x)) =
      zeroCoordinates c A 0
    rw [map_zero, connectingMap_coordinates, ((zFreeData c A).data).complex_d 0]
    exact congrArg (fun f => (f x : FiniteResolution.zImage c).val) ((zFreeData c A).data).d_ε
  d₀_comp := by
    ext x
    apply (oneCoordinates c A).injective
    change oneCoordinates c A ((dual c A).d 0 1 (connectingMap c A x)) =
      oneCoordinates c A 0
    rw [map_zero, dual_d_zero_one, connectingMap_coordinates]
    exact (c.exact_X hc _).mpr ⟨x, rfl⟩

/-- The actual integer-indexed finite free model, with qudits in degree zero. -/
def complex (c : CSS.Checks K D q s r) (A : Input c) (hc : c.Topological) :
    CochainComplex (ModuleCat (Laurent K D)) ℤ :=
  (connection c A hc).cochainComplex

@[simp] theorem complex_X_nonneg (c : CSS.Checks K D q s r) (A : Input c) (hc : c.Topological)
    (n : ℕ) : (complex c A hc).X n = (dual c A).X n := rfl

@[simp] theorem complex_X_negSucc (c : CSS.Checks K D q s r) (A : Input c) (hc : c.Topological)
    (n : ℕ) : (complex c A hc).X (Int.negSucc n) = ((zFreeData c A).data).X n := rfl

@[simp] theorem complex_d_zero_one (c : CSS.Checks K D q s r) (A : Input c) (hc : c.Topological) :
    (complex c A hc).d 0 1 = (dual c A).d 0 1 := rfl

@[simp] theorem complex_d_minus_one_zero (c : CSS.Checks K D q s r) (A : Input c)
    (hc : c.Topological) : (complex c A hc).d (-1) 0 = connectingMap c A := rfl

@[simp] theorem complex_d_one_two (c : CSS.Checks K D q s r) (A : Input c)
    (hc : c.Topological) : (complex c A hc).d 1 2 = (dual c A).d 1 2 := rfl

/-- The actual degree-minus-one differential is the supplied Z dagger. -/
theorem complex_Z_window (c : CSS.Checks K D q s r) (A : Input c)
    (hc : c.Topological) (x : CSS.Free K D r) :
    zeroCoordinates c A ((complex c A hc).d (-1) 0 x) = dagger c.H_Z *ᵥ x :=
  connectingMap_coordinates c A x

/-- The actual degree-zero differential is the supplied X check. -/
theorem complex_X_window (c : CSS.Checks K D q s r) (A : Input c)
    (hc : c.Topological) (x : (complex c A hc).X 0) :
    oneCoordinates c A ((complex c A hc).d 0 1 x) = c.H_X *ᵥ zeroCoordinates c A x :=
  dual_d_zero_one c A x

/-- The actual next differential retains the supplied gamma matrix. -/
theorem complex_gamma_window (c : CSS.Checks K D q s r) (A : Input c)
    (hc : c.Topological) (x : (complex c A hc).X 1) :
    twoCoordinates c A ((complex c A hc).d 1 2 x) = A.gamma *ᵥ oneCoordinates c A x :=
  dual_d_one_two c A x

instance complex_finite (c : CSS.Checks K D q s r) (A : Input c) (hc : c.Topological) (n : ℤ) :
    Module.Finite (Laurent K D) ((complex c A hc).X n) := by
  cases n with
  | ofNat n => exact dual_finite c A n
  | negSucc n => exact ((zFreeData c A).data).finite n

instance complex_free (c : CSS.Checks K D q s r) (A : Input c) (hc : c.Topological) (n : ℤ) :
    Module.Free (Laurent K D) ((complex c A hc).X n) := by
  cases n with
  | ofNat n => exact dual_free c A n
  | negSucc n => exact (zFreeData c A).free n

instance complex_projective (c : CSS.Checks K D q s r) (A : Input c) (hc : c.Topological) (n : ℤ) :
    Projective ((complex c A hc).X n) := inferInstance

theorem complex_boundedAbove (c : CSS.Checks K D q s r) (A : Input c) (hc : c.Topological) (hD : 1 ≤ D) :
    (complex c A hc).IsStrictlyLE (D + 2) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  cases n with
  | ofNat n => exact dual_zero_above c A hD n (by simp only [Int.ofNat_eq_natCast] at hn; omega)
  | negSucc n => omega

instance complex_boundedBelow (c : CSS.Checks K D q s r) (A : Input c) (hc : c.Topological) :
    (complex c A hc).IsStrictlyGE (-(D + 2 : ℕ)) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro n hn
  cases n with
  | ofNat n => simp only [Int.ofNat_eq_natCast] at hn; omega
  | negSucc n => exact ((zFreeData c A).data).zero_above n (by omega)

theorem complex_exact_zero (c : CSS.Checks K D q s r) (A : Input c) (hc : c.Topological) :
    (complex c A hc).ExactAt 0 := by
  rw [(complex c A hc).exactAt_iff' (-1) 0 1 (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  have hx' : c.H_X *ᵥ zeroCoordinates c A x = 0 := by
    rw [← dual_d_zero_one]
    exact congrArg (oneCoordinates c A) hx
  obtain ⟨z, hz⟩ := (c.exact_X hc _).mp hx'
  refine ⟨z, ?_⟩
  apply (zeroCoordinates c A).injective
  change zeroCoordinates c A (connectingMap c A z) = _
  rw [connectingMap_coordinates]
  exact hz

theorem complex_exact_minus_one (c : CSS.Checks K D q s r) (A : Input c)
    (hc : c.Topological) : (complex c A hc).ExactAt (-1) := by
  rw [(complex c A hc).exactAt_iff' (-2) (-1) 0 (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  have hx' : ((zFreeData c A).data).ε x = 0 := by
    apply Subtype.ext
    have hh := congrArg (zeroCoordinates c A) hx
    change zeroCoordinates c A (connectingMap c A x) = zeroCoordinates c A 0 at hh
    rw [connectingMap_coordinates, map_zero] at hh
    exact hh
  have hxmem : x ∈ LinearMap.range (((zFreeData c A).data).d 0).hom := by
    rw [((zFreeData c A).data).exact_zero]
    exact hx'
  exact hxmem

theorem complex_exact_negative (c : CSS.Checks K D q s r) (A : Input c)
    (hc : c.Topological) (n : ℕ) : (complex c A hc).ExactAt (Int.negSucc (n + 1)) := by
  rw [(complex c A hc).exactAt_iff' (Int.negSucc (n + 2))
    (Int.negSucc (n + 1)) (Int.negSucc n) (by simp) (by simp; omega)]
  apply (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mpr
  simpa only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor',
    complex, CochainComplex.ConnectData.cochainComplex_d,
    CochainComplex.ConnectData.d_negSucc, FiniteResolution.Data.complex_d] using ((zFreeData c A).data).exact_succ n

instance complex_isGE (c : CSS.Checks K D q s r) (A : Input c) (hc : c.Topological) :
    (complex c A hc).IsGE 1 := by
  rw [CochainComplex.isGE_iff]
  intro n hn
  cases n with
  | ofNat n =>
    have : n = 0 := by simp only [Int.ofNat_eq_natCast] at hn; omega
    subst this
    exact complex_exact_zero c A hc
  | negSucc n =>
    cases n with
    | zero => exact complex_exact_minus_one c A hc
    | succ n => exact complex_exact_negative c A hc n

/-- Positive homology of the connected model is the actual native Ext. -/
def complex_positiveHomologyEquivExt (c : CSS.Checks K D q s r) (A : Input c)
    (hc : c.Topological) (n : ℕ) :
    (complex c A hc).homology (n + 1 : ℕ) ≃ₗ[Laurent K D] Layers.E_X c (n + 1) :=
  ((connection c A hc).homologyIsoPos (n + 1) (n + 1 : ℕ) rfl).toLinearEquiv.trans
    (ResolutionCohomology.homologyEquivExt (conjugateResolution c A)
      (ModuleCat.of (Laurent K D) (Laurent K D)) n)


end
end Decoupling.HighDim.SchreyerCSS
