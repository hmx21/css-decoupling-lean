import Decoupling.HighDim.AlgorithmTwoComputedLayersFormality
import Decoupling.HighDim.AlgorithmTwoComputedLayersWindow

/-!
# The computed cohomology outputs determine the new toric comparison

Each dimension and each cocycle comes from the actual cohomology
program. The native bases selected below are proof witnesses for
those same stored cocycles, not runtime basis choices. The original
formal multiplicities need not be supplied as the computed ones.
-/
namespace Decoupling.HighDim.AlgorithmTwoComputedLayers
open CategoryTheory HomologicalComplex Matrix
open AlgorithmTwoComparison AlgorithmTwoCohomology CohomologyPresentation
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
attribute [local instance] HasDerivedCategory.standard
variable {K : Type} [Field K] [DecidableEq K] {D h : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (cC : StableFree.Coordinates C)
  (old : Fin (D - 1) → ℕ)
  (e : DerivedCategory.Q.obj (Toric.stackModel K D (Toric.copyForms D old)) ≅ DerivedCategory.Q.obj C)
  (b : ∀ j : Fin (D - 1), LaurentArithmetic.DenseMatrix K D (cC.rank (j.val + 1))
    (cC.rank ((j.val : ℤ) + 1 - 1)) h)
  (d : ∀ j : Fin (D - 1), LaurentArithmetic.DenseMatrix K D (cC.rank ((j.val : ℤ) + 1 + 1))
    (cC.rank (j.val + 1)) h)
  (hb : ∀ (j : Fin (D - 1)) x,
    LaurentArithmetic.matrixDenote (b j) *ᵥ cC.equiv ((j.val : ℤ) + 1 - 1) x =
      cC.equiv (j.val + 1) (C.d ((j.val : ℤ) + 1 - 1) (j.val + 1) x))
  (hd : ∀ (j : Fin (D - 1)) x,
    LaurentArithmetic.matrixDenote (d j) *ᵥ cC.equiv (j.val + 1) x =
      cC.equiv ((j.val : ℤ) + 1 + 1) (C.d (j.val + 1) ((j.val : ℤ) + 1 + 1) x))

def output (j : Fin (D - 1)) :
    Result K D (cC.rank (j.val + 1))
      (LaurentLinearSolver.outputBox D (cC.rank ((j.val : ℤ) + 1 + 1)) h) :=
  (compute (b j) (d j)).value

def outputMultiplicities : Fin (D - 1) → ℕ := fun j => (output cC b d j).dimension

omit [DecidableEq K] in
include hb hd in
theorem outputWindowSquare (j : Fin (D - 1)) :
    LaurentArithmetic.matrixDenote (d j) * LaurentArithmetic.matrixDenote (b j) = 0 :=
  window_product_zero cC (j.val + 1) _ _ (hb j) (hd j)

include old e hb hd

theorem output_correct (j : Fin (D - 1)) :
    Correct (LaurentArithmetic.matrixDenote (b j)) (LaurentArithmetic.matrixDenote (d j))
      (outputWindowSquare cC b d hb hd j) (output cC b d j) := by
  apply compute_correct
  apply TrivialLayers.augmentationAction_of_iso
    (windowNativeIso cC (j.val + 1) _ _ (hb j) (hd j) (outputWindowSquare cC b d hb hd j))
  exact nativeHomology_augmentation K D old e (j.val + 1)

def outputCycle (j : Fin (D - 1)) (k : Fin (outputMultiplicities cC b d j)) : C.X (j.val + 1) :=
  decodedCocycle cC (j.val + 1) (output cC b d j) k

theorem outputCycle_closed (j : Fin (D - 1)) (k : Fin (outputMultiplicities cC b d j)) :
    C.d (j.val + 1) ((j.val : ℤ) + 1 + 1) (outputCycle cC b d j k) = 0 :=
  decoded_cycle_closed cC (j.val + 1) _ (hd j) _
    ((output_correct cC old e b d hb hd j).closed k)

def outputBasis (j : Fin (D - 1)) :
    Module.Basis (Fin (outputMultiplicities cC b d j)) K (Layers.coefficients (C.homology (j.val + 1))) :=
  ((output_correct cC old e b d hb hd j).basis.choose).map
    (((ModuleCat.restrictScalars (constant : K →+* Laurent K D)).mapIso
      (windowNativeIso cC (j.val + 1) _ _ (hb j) (hd j)
        (outputWindowSquare cC b d hb hd j))).toLinearEquiv)

theorem outputBasis_apply (j : Fin (D - 1)) (k : Fin (outputMultiplicities cC b d j)) :
    outputBasis cC old e b d hb hd j k =
      nativeCycleClass C (j.val + 1) (outputCycle cC b d j k)
        (outputCycle_closed cC old e b d hb hd j k) := by
  change (windowNativeIso cC (j.val + 1) _ _ (hb j) (hd j)
    (outputWindowSquare cC b d hb hd j)).hom ((output_correct cC old e b d hb hd j).basis.choose k) = _
  rw [(output_correct cC old e b d hb hd j).basis.choose_spec]
  exact windowNativeIso_cycle cC (j.val + 1) _ _ (hb j) (hd j) _ _ _

include old e hb hd in
/-- The actual output multiplicities and stored output cocycles admit
the prescribed native comparison; no output correctness certificate
is an input to this theorem. -/
theorem program_comparison_exists :
    ∃ g : Toric.stackModel K D (Toric.copyForms D (outputMultiplicities cC b d)) ⟶ C, QuasiIso g ∧
      ∀ (j : Fin (D - 1)) (k : Fin (outputMultiplicities cC b d j)),
        g.f (j.val + 1) (stackTop K D (Toric.copyForms D (outputMultiplicities cC b d)) ⟨j, k⟩) =
          outputCycle cC b d j k :=
  exists_computed_comparison K D old e (outputMultiplicities cC b d)
    (outputBasis cC old e b d hb hd) (outputCycle cC b d)
    (outputCycle_closed cC old e b d hb hd) (outputBasis_apply cC old e b d hb hd)

include old e hb hd in
theorem program_solution_quasiIso
    (g : Toric.stackModel K D (Toric.copyForms D (outputMultiplicities cC b d)) ⟶ C)
    (htop : ∀ (j : Fin (D - 1)) (k : Fin (outputMultiplicities cC b d j)),
      g.f (j.val + 1) (stackTop K D (Toric.copyForms D (outputMultiplicities cC b d)) ⟨j, k⟩) =
        outputCycle cC b d j k) : QuasiIso g :=
  computed_solution_quasiIso K D old e (outputMultiplicities cC b d)
    (outputBasis cC old e b d hb hd) (outputCycle cC b d)
    (outputCycle_closed cC old e b d hb hd) (outputBasis_apply cC old e b d hb hd) g htop

end
end Decoupling.HighDim.AlgorithmTwoComputedLayers
