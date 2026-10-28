import Decoupling.HighDim.AlgorithmTwoComparisonLift
import Decoupling.HighDim.ToricStack

/-!
# Actual empty-cell generators and their simultaneous correction

The distinguished source cycles are the actual empty Koszul cells in
the individual toric summands. The homotopy is extended from those
cells by the degree-zero Koszul coordinate, then combined using the
actual biproduct projections. No extension of a partial basis is
assumed.
-/
namespace Decoupling.HighDim.AlgorithmTwoComparison
open CategoryTheory CategoryTheory.Limits HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
attribute [local instance] HasDerivedCategory.standard
variable (K : Type) [Field K] (D : ℕ)

def toricTopEquiv (j : ℤ) :
    (Toric.model K D j).X j ≃ₗ[Laurent K D] Laurent K D :=
  ((Koszul.laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE j)
    (i := 0) (i' := j) (by simp)).toLinearEquiv.trans (Koszul.zeroTermEquiv (Laurent K D))

def toricTop (j : ℤ) : (Toric.model K D j).X j := (toricTopEquiv K D j).symm 1

theorem toricTop_closed (j : ℤ) :
    (Toric.model K D j).d j (j + 1) (toricTop K D j) = 0 := by
  have hz := (Toric.model K D j).isZero_of_isStrictlyLE j (j + 1) (by omega)
  exact (ModuleCat.subsingleton_of_isZero hz).elim _ _

variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}

def toricBoundaryHomotopy (j : ℤ) (z : C.X (j - 1)) :
    ∀ n, (Toric.model K D j).X n ⟶ C.X (n - 1) :=
  Function.update (fun _ => 0) j
    (ModuleCat.ofHom ((toricTopEquiv K D j).toLinearMap.smulRight z))

theorem toricBoundaryHomotopy_top (j : ℤ) (z : C.X (j - 1)) :
    toricBoundaryHomotopy K D j z j (toricTop K D j) = z := by
  simp [toricBoundaryHomotopy, toricTop]

local instance : HasFiniteBiproducts (CochainComplex (ModuleCat (Laurent K D)) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

variable {ι : Type} [Fintype ι] (forms : ι → ℕ)

def stackTop (i : ι) : (Toric.stackModel K D forms).X (forms i + 1) :=
  (biproduct.ι (fun i => Toric.model K D (forms i + 1)) i).f (forms i + 1)
    (toricTop K D (forms i + 1))

theorem stackTop_closed (i : ι) :
    (Toric.stackModel K D forms).d (forms i + 1) (((forms i : ℤ) + 1) + 1)
      (stackTop K D forms i) = 0 := by
  let a := biproduct.ι (fun i => Toric.model K D (forms i + 1)) i
  change (a.f (forms i + 1) ≫ (Toric.stackModel K D forms).d _ _)
    (toricTop K D (forms i + 1)) = 0
  dsimp only [Toric.stackModel]
  rw [a.comm]
  change a.f _ ((Toric.model K D (forms i + 1)).d _ _ (toricTop K D (forms i + 1))) = 0
  rw [toricTop_closed, map_zero]

def stackBoundaryHomotopy
    (z : ∀ i, C.X (((forms i : ℤ) + 1) - 1)) :
    ∀ n, (Toric.stackModel K D forms).X n ⟶ C.X (n - 1) :=
  fun n => ∑ i, (biproduct.π (fun i => Toric.model K D (forms i + 1)) i).f n ≫
    toricBoundaryHomotopy K D (forms i + 1) (z i) n

theorem stackBoundaryHomotopy_top
    (z : ∀ i, C.X (((forms i : ℤ) + 1) - 1)) (i : ι) :
    stackBoundaryHomotopy K D forms z (forms i + 1) (stackTop K D forms i) = z i := by
  classical
  let M := fun i => Toric.model K D (forms i + 1)
  have he : (biproduct.ι M i).f (forms i + 1) ≫ stackBoundaryHomotopy K D forms z (forms i + 1) =
      toricBoundaryHomotopy K D (forms i + 1) (z i) (forms i + 1) := by
    dsimp only [stackBoundaryHomotopy]
    rw [Preadditive.comp_sum]
    dsimp only [M]
    rw [Finset.sum_eq_single i]
    · simp only [← Category.assoc, ← HomologicalComplex.comp_f, biproduct.ι_π_self,
        HomologicalComplex.id_f, Category.id_comp]
    · intro k _ hki
      rw [← Category.assoc, ← HomologicalComplex.comp_f, biproduct.ι_π_ne _ (Ne.symm hki)]
      simp
    · simp
  change ((biproduct.ι M i).f (forms i + 1) ≫ stackBoundaryHomotopy K D forms z (forms i + 1))
    (toricTop K D (forms i + 1)) = _
  rw [he, toricBoundaryHomotopy_top]

/-- Once the map on native homology has been normalised, all actual
empty-cell values can be prescribed simultaneously and exactly. -/
theorem exists_stack_prescribed
    (f : Toric.stackModel K D forms ⟶ C) [QuasiIso f]
    (c : ∀ i, C.X (forms i + 1))
    (hc : ∀ i, C.d (forms i + 1) (((forms i : ℤ) + 1) + 1) (c i) = 0)
    (hclass : ∀ i, nativeCycleClass C (forms i + 1) (c i) (hc i) =
      nativeCycleClass C (forms i + 1) (f.f (forms i + 1) (stackTop K D forms i)) (by
        change (f.f (forms i + 1) ≫ C.d _ _) (stackTop K D forms i) = 0
        rw [f.comm]
        change f.f _ ((Toric.stackModel K D forms).d _ _ (stackTop K D forms i)) = 0
        rw [stackTop_closed, map_zero])) :
    ∃ g : Toric.stackModel K D forms ⟶ C, QuasiIso g ∧ Nonempty (Homotopy g f) ∧
      ∀ i, g.f (forms i + 1) (stackTop K D forms i) = c i := by
  have hz : ∀ i, ∃ z : C.X (((forms i : ℤ) + 1) - 1),
      C.d (((forms i : ℤ) + 1) - 1) (forms i + 1) z =
        c i - f.f (forms i + 1) (stackTop K D forms i) :=
    fun i => (nativeCycleClass_eq_iff C (forms i + 1) _ _ _ _).mp (hclass i)
  choose z hz using hz
  let h := stackBoundaryHomotopy K D forms z
  refine ⟨correctedMap f h, quasiIso_of_homotopy (correctedMapHomotopy f h),
    ⟨correctedMapHomotopy f h⟩, ?_⟩
  intro i
  apply correctedMap_prescribed f h (forms i + 1) _ (stackTop_closed K D forms i)
  rw [show h (forms i + 1) (stackTop K D forms i) = z i from
    stackBoundaryHomotopy_top K D forms z i]
  exact hz i

end
end Decoupling.HighDim.AlgorithmTwoComparison
