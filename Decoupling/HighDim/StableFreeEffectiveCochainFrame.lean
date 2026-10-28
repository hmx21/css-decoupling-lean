import Decoupling.HighDim.AlgorithmTwoFiniteComplexSliceMap
import Decoupling.HighDim.StableFreeEffectiveCochainSequence

/-!
# Original-term selectors into arbitrary actual total coordinate frames

The target may use copy-major toric order and the source degree-major order.
Selectors only copy original coefficients; their contracts identify the
original basis vectors. No change of field basis or matrix solve is hidden.
-/
namespace Decoupling.HighDim.StableFree.Effective.CochainProgram
open Matrix LaurentArithmetic AlgorithmTwoFiniteComplex
universe u
variable {K : Type u} [Field K] {D h : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Actual integer lookup tables for original term coordinates. -/
structure TermSelectors (rank : ℤ → ℕ) (total : ℕ) where
  atDegree : ∀ j, Vector (Fin total) (rank j)

def originalSlice {rC rT : ℤ → ℕ} {n m : ℕ}
    (sC : TermSelectors rC n) (sT : TermSelectors rT m) (b a : ℤ)
    (A : DenseMatrix K D n m h) : DenseMatrix K D (rC b) (rT a) h :=
  sliceMap A (sC.atDegree b) (sT.atDegree a)

/-- Pure original negative differential slices used by the full recursion. -/
def tailArrays {rank : ℤ → ℕ} {n : ℕ} (s : TermSelectors rank n)
    (A : DenseMatrix K D n n h) (i : ℕ) :
    DenseMatrix K D (rank (1-(i:ℤ))) (rank (1-(i+1:ℕ))) h :=
  originalSlice s s (1-(i:ℤ)) (1-(i+1:ℕ)) A

def tailTower {rank : ℤ → ℕ} {n : ℕ} (s : TermSelectors rank n)
    (A : DenseMatrix K D n n h) (length : ℕ) : DenseTower K D h length (rank 1) :=
  DenseTower.ofDifferentials (fun i => rank (1-(i:ℤ))) (tailArrays s A) length

noncomputable section
variable {C T : CochainComplex (ModuleCat.{u} (Laurent K D)) ℤ} {n m : ℕ}

/-- Exact original-coordinate contracts; these are solely representation
facts about the given total frame and given selector tables. -/
structure FrameRealizes (c : StableFree.Coordinates C)
    (frame : AlgorithmTwoFiniteComplex.Coordinates C n) (s : TermSelectors c.rank n) : Prop where
  rows : ∀ j x i, frame.embed j x ((s.atDegree j).get i) = c.equiv j x i
  columns : ∀ j i, frame.embed j ((c.equiv j).symm (Pi.single i 1)) =
    Pi.single ((s.atDegree j).get i) 1

theorem originalSlice_native (cC : StableFree.Coordinates C) (cT : StableFree.Coordinates T)
    (frameC : AlgorithmTwoFiniteComplex.Coordinates C n) (frameT : AlgorithmTwoFiniteComplex.Coordinates T m)
    (sC : TermSelectors cC.rank n) (sT : TermSelectors cT.rank m)
    (hC : FrameRealizes cC frameC sC) (hT : FrameRealizes cT frameT sT)
    (b a : ℤ) (A : DenseMatrix K D n m h) (f : T.X a →ₗ[Laurent K D] C.X b)
    (hA : ∀ x, matrixDenote A *ᵥ frameT.embed a x = frameC.embed b (f x)) :
    matrixDenote (originalSlice sC sT b a A) =
      LinearMap.toMatrix' ((cC.equiv b).toLinearMap.comp (f.comp (cT.equiv a).symm.toLinearMap)) := by
  apply Matrix.mulVec_injective
  funext x
  obtain ⟨x,rfl⟩ := (cT.equiv a).surjective x
  rw [LinearMap.toMatrix'_mulVec]
  change matrixDenote (sliceMap A (sC.atDegree b) (sT.atDegree a)) *ᵥ cT.equiv a x =
    cC.equiv b (f ((cT.equiv a).symm (cT.equiv a x)))
  rw [LinearEquiv.symm_apply_apply]
  exact sliceMap_native frameT frameC a b (cT.equiv a) (cC.equiv b)
    _ _ (hC.rows b) (hT.columns a) A f hA x

theorem tailArrays_native (c : StableFree.Coordinates C)
    (frame : AlgorithmTwoFiniteComplex.Coordinates C n) (s : TermSelectors c.rank n)
    (hs : FrameRealizes c frame s) (A : DenseMatrix K D n n h)
    (hA : frame.RepresentsDifferential (matrixDenote A)) (i : ℕ) :
    matrixDenote (tailArrays s A i) = LinearMap.toMatrix'
      ((c.equiv (1-(i:ℤ))).toLinearMap.comp
        ((C.d (1-(i+1:ℕ)) (1-(i:ℤ))).hom.comp (c.equiv (1-(i+1:ℕ))).symm.toLinearMap)) := by
  apply originalSlice_native c c frame frame s s hs hs
  exact represents_at frame _ hA _ _ (by omega)

/-- Native cochain exactness and the actual lower support bound establish
all kernel-cover semantics of the stored tail slices. -/
theorem tailTower_models (c : StableFree.Coordinates C)
    (frame : AlgorithmTwoFiniteComplex.Coordinates C n) (s : TermSelectors c.rank n)
    (hs : FrameRealizes c frame s) (A : DenseMatrix K D n n h)
    (hA : frame.RepresentsDifferential (matrixDenote A)) (l : ℕ)
    [C.IsGE 1] [C.IsStrictlyGE (-(l:ℤ))] :
    DenseTower.Models (tailTower s A (l+1))
      (ModuleCat.of (Laurent K D) (LinearMap.ker
        (((LinearMap.range (C.d 0 1).hom).mkQ).comp (c.equiv 1).symm.toLinearMap)))
      (LinearMap.ker (((LinearMap.range (C.d 0 1).hom).mkQ).comp (c.equiv 1).symm.toLinearMap)).subtype := by
  apply coordinateSequence_models (StableFree.checkSequence C c (StableFree.nonpositive_exact C))
    (tailArrays s A)
  · intro i
    exact tailArrays_native c frame s hs A hA i
  · intro i hi
    exact C.isZero_of_isStrictlyGE (-(l:ℤ)) (1-(i:ℤ)) (by omega)

end
end Decoupling.HighDim.StableFree.Effective.CochainProgram
