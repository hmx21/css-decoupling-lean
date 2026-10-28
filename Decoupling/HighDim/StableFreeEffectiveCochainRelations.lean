import Decoupling.HighDim.StableFreeEffectiveCochainInputs
import Decoupling.HighDim.StableFreeEffectiveQuotient

/-!
# Actual stabilized check presentations in the original coordinates

The free rows are appended to the real d^0 matrix by coefficient copying.
The kernel of the actual quotient augmentation is proved to be exactly its
range, so comparison lifting can consume these arrays directly.
-/
namespace Decoupling.HighDim.StableFree.Effective.CochainProgram
open Matrix LaurentArithmetic HomologicalComplex
universe u
variable {K : Type u} [Field K] {D h H n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Original d^0 rows followed by the actual adjoined free rows. -/
def augmentedRelations {rank : ℤ → ℕ} (s : TermSelectors rank n)
    (A : DenseMatrix K D n n h) (extra H : ℕ) :
    DenseMatrix K D (rank 1+extra) (rank 0) H :=
  matrixPad (rowBlocksDense (originalSlice s s 1 0 A) (zeroMatrixDense K D h extra (rank 0))) H

theorem augmentedRelations_correct {rank : ℤ → ℕ} (s : TermSelectors rank n)
    (A : DenseMatrix K D n n h) (extra : ℕ) (hh : h ≤ H) :
    matrixDenote (augmentedRelations s A extra H) =
      stabilizedRelations (matrixDenote (originalSlice s s 1 0 A)) extra := by
  rw [augmentedRelations,matrixPad_correct _ hh,rowBlocksDense_correct,zeroMatrixDense_correct]
  rfl

noncomputable section
variable {C : CochainComplex (ModuleCat.{u} (Laurent K D)) ℤ}

def checkQuotient (c : StableFree.Coordinates C) :
    Power (Laurent K D) (c.rank 1) →ₗ[Laurent K D] CochainCokernel.CheckCokernel C :=
  ((LinearMap.range (C.d 0 1).hom).mkQ).comp (c.equiv 1).symm.toLinearMap

theorem checkQuotient_surjective (c : StableFree.Coordinates C) :
    Function.Surjective (checkQuotient c) :=
  (LinearMap.range (C.d 0 1).hom).mkQ_surjective.comp (c.equiv 1).symm.surjective

theorem checkQuotient_kernel (c : StableFree.Coordinates C)
    (frame : AlgorithmTwoFiniteComplex.Coordinates C n) (s : TermSelectors c.rank n)
    (hs : FrameRealizes c frame s) (A : DenseMatrix K D n n h)
    (hA : frame.RepresentsDifferential (matrixDenote A)) :
    LinearMap.ker (checkQuotient c) = LinearMap.range (matrixDenote (originalSlice s s 1 0 A)).mulVecLin := by
  rw [originalSlice_native c c frame frame s s hs hs 1 0 A _
    (AlgorithmTwoFiniteComplex.represents_at frame _ hA 0 1 rfl)]
  exact (Initial.homotopyData (HomotopyEquiv.refl C) c c).kerN

/-- Exact augmentation consumed by the four actual comparison systems. -/
theorem augmentedRelations_kernel (c : StableFree.Coordinates C)
    (frame : AlgorithmTwoFiniteComplex.Coordinates C n) (s : TermSelectors c.rank n)
    (hs : FrameRealizes c frame s) (A : DenseMatrix K D n n h)
    (hA : frame.RepresentsDifferential (matrixDenote A)) (extra : ℕ) (hh : h ≤ H) :
    LinearMap.ker (stabilizedQuotient (N := ModuleCat.of (Laurent K D) (CochainCokernel.CheckCokernel C)) (checkQuotient c) extra) =
      LinearMap.range (matrixDenote (augmentedRelations s A extra H)).mulVecLin := by
  rw [augmentedRelations_correct s A extra hh]
  exact stabilizedQuotient_kernel (N := ModuleCat.of (Laurent K D) (CochainCokernel.CheckCokernel C)) _ _ (checkQuotient_kernel c frame s hs A hA) extra

theorem augmentedQuotient_surjective (c : StableFree.Coordinates C) (extra : ℕ) :
    Function.Surjective (stabilizedQuotient (N := ModuleCat.of (Laurent K D) (CochainCokernel.CheckCokernel C)) (checkQuotient c) extra) :=
  stabilizedQuotient_surjective (N := ModuleCat.of (Laurent K D) (CochainCokernel.CheckCokernel C)) _ (checkQuotient_surjective c) extra

end
end Decoupling.HighDim.StableFree.Effective.CochainProgram
