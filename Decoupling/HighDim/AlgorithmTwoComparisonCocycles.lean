import Decoupling.HighDim.AlgorithmTwoComparisonCorrection

/-!
# Simultaneous prescription of chosen basis cycles

The free coordinates are coordinates of the supplied complex terms.
Only selected basis vectors which are cycles are prescribed. Equality
of their native homology classes supplies genuine boundaries, and the
constructed cochain homotopy removes all those boundaries at once.
This proves solvability of the prescribed linear equations; it is not
a claimed executable choice of a boundary or a cost estimate.
-/
namespace Decoupling.HighDim.AlgorithmTwoComparison
open CategoryTheory HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
variable {R : Type} [CommRing R]

def cycleHomologyIso (C : CochainComplex (ModuleCat R) ℤ) (j : ℤ) :
    C.homology j ≅ (C.sc' (j - 1) j (j + 1)).homology :=
  (homologyFunctorIso' (ModuleCat R) (ComplexShape.up ℤ) (j - 1) j (j + 1)
    (by simp) (by simp)).app C

/-- A concrete cycle, as an element of the actual native cohomology. -/
def nativeCycleClass (C : CochainComplex (ModuleCat R) ℤ) (j : ℤ) (x : C.X j)
    (hx : C.d j (j + 1) x = 0) : C.homology j :=
  (cycleHomologyIso C j).inv (Glued.cycleClass (C.sc' (j - 1) j (j + 1)) x hx)

theorem nativeCycleClass_eq_iff (C : CochainComplex (ModuleCat R) ℤ) (j : ℤ)
    (x y : C.X j) (hx : C.d j (j + 1) x = 0) (hy : C.d j (j + 1) y = 0) :
    nativeCycleClass C j x hx = nativeCycleClass C j y hy ↔
      ∃ z : C.X (j - 1), C.d (j - 1) j z = x - y := by
  let S := C.sc' (j - 1) j (j + 1)
  change (cycleHomologyIso C j).symm.toLinearEquiv (Glued.cycleClass S x hx) =
    (cycleHomologyIso C j).symm.toLinearEquiv (Glued.cycleClass S y hy) ↔ _
  rw [(cycleHomologyIso C j).symm.toLinearEquiv.injective.eq_iff]
  rw [← (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance |>.eq_iff,
    Glued.cycleClass_ι, Glued.cycleClass_ι, ← sub_eq_zero, ← map_sub,
    ShortComplex.moduleCat_pOpcycles_eq_zero_iff]
  rfl

def coordinateBasis {T : CochainComplex (ModuleCat R) ℤ} (cT : StableFree.Coordinates T) (j : ℤ) :
    Module.Basis (Fin (cT.rank j)) R (T.X j) :=
  (Pi.basisFun R _).map (cT.equiv j).symm

variable {T C : CochainComplex (ModuleCat R) ℤ}

theorem nativeCycleClass_naturality (f : T ⟶ C) (j : ℤ) (x : T.X j)
    (hx : T.d j (j + 1) x = 0) :
    homologyMap f j (nativeCycleClass T j x hx) =
      nativeCycleClass C j (f.f j x) (by
        change (f.f j ≫ C.d j (j + 1)) x = 0
        rw [f.comm]
        change f.f (j + 1) (T.d j (j + 1) x) = 0
        rw [hx, map_zero]) := by
  let I := homologyFunctorIso' (ModuleCat R) (ComplexShape.up ℤ) (j - 1) j (j + 1)
    (by simp) (by simp)
  have hn := I.inv.naturality f
  change (ShortComplex.homologyMap ((shortComplexFunctor' _ _ (j - 1) j (j + 1)).map f)) ≫
    (cycleHomologyIso C j).inv = (cycleHomologyIso T j).inv ≫ homologyMap f j at hn
  change ((cycleHomologyIso T j).inv ≫ homologyMap f j)
    (Glued.cycleClass (T.sc' (j - 1) j (j + 1)) x hx) = _
  rw [← hn]
  change (cycleHomologyIso C j).inv
    (ShortComplex.homologyMap ((shortComplexFunctor' _ _ (j - 1) j (j + 1)).map f)
      (Glued.cycleClass (T.sc' (j - 1) j (j + 1)) x hx)) = _
  rw [Glued.homologyMap_cycleClass]
  rfl

theorem exists_prescribed_map (f : T ⟶ C) (cT : StableFree.Coordinates T)
    (P : ∀ j, Fin (cT.rank j) → Prop)
    (sourceClosed : ∀ j k, P j k → T.d j (j + 1) (coordinateBasis cT j k) = 0)
    (c : ∀ j, Fin (cT.rank j) → C.X j)
    (targetClosed : ∀ j k, P j k → C.d j (j + 1) (c j k) = 0)
    (classes : ∀ j k (hk : P j k),
      nativeCycleClass C j (c j k) (targetClosed j k hk) =
        nativeCycleClass C j (f.f j (coordinateBasis cT j k)) (by
          change (f.f j ≫ C.d j (j + 1)) (coordinateBasis cT j k) = 0
          rw [f.comm]
          change f.f (j + 1) (T.d j (j + 1) (coordinateBasis cT j k)) = 0
          rw [sourceClosed j k hk, map_zero])) :
    ∃ g : T ⟶ C, Nonempty (Homotopy g f) ∧
      ∀ j k, P j k → g.f j (coordinateBasis cT j k) = c j k := by
  classical
  have hb : ∀ j k, P j k → ∃ z : C.X (j - 1),
      C.d (j - 1) j z = c j k - f.f j (coordinateBasis cT j k) :=
    fun j k hk => (nativeCycleClass_eq_iff C j _ _ _ _).mp (classes j k hk)
  let w : ∀ j, Fin (cT.rank j) → C.X (j - 1) :=
    fun j k => if hk : P j k then (hb j k hk).choose else 0
  let h : ∀ j, T.X j ⟶ C.X (j - 1) :=
    fun j => ModuleCat.ofHom ((coordinateBasis cT j).constr R (w j))
  refine ⟨correctedMap f h, ⟨correctedMapHomotopy f h⟩, ?_⟩
  intro j k hk
  apply correctedMap_prescribed f h j _ (sourceClosed j k hk)
  change C.d (j - 1) j ((coordinateBasis cT j).constr R (w j) (coordinateBasis cT j k)) = _
  rw [Module.Basis.constr_basis]
  dsimp only [w]
  rw [dite_eq_left hk]
  exact (hb j k hk).choose_spec

end
end Decoupling.HighDim.AlgorithmTwoComparison
