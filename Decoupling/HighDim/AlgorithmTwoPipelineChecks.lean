import Decoupling.HighDim.AlgorithmTwoPipelineProgram
import Decoupling.HighDim.AlgorithmTwoPhysicalTransportComputed

/-! # Actual original-coordinate checks and identity rows returned by C4 -/
namespace Decoupling.HighDim.AlgorithmTwoPipeline
open CategoryTheory HomologicalComplex Matrix ArithmeticCost AlgorithmTwoFiniteComplex
open StableFree.Effective StableFree.Effective.CochainProgram
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
variable {K : Type} [Field K] {D : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}

/-- Original term coordinates of the actual differential. -/
def degreeMatrix (c : StableFree.Coordinates C) (a b : ℤ) :
    Matrix (Fin (c.rank b)) (Fin (c.rank a)) (Laurent K D) :=
  LinearMap.toMatrix' ((c.equiv b).toLinearMap.comp ((C.d a b).hom.comp (c.equiv a).symm.toLinearMap))

theorem degreeMatrix_action (c : StableFree.Coordinates C) (a b : ℤ) (v : Fin (c.rank a) → Laurent K D) :
    degreeMatrix c a b *ᵥ v = c.equiv b ((C.d a b).hom ((c.equiv a).symm v)) :=
  LinearMap.toMatrix'_mulVec _ v

/-- Native exactness at degree zero gives the actual CSS X-kernel equality. -/
theorem degreeMatrix_exact_zero (c : StableFree.Coordinates C) [C.IsGE 1]
    (v : Fin (c.rank 0) → Laurent K D) :
    degreeMatrix c 0 1 *ᵥ v = 0 ↔ PhysicalIsomorphism.inImage (degreeMatrix c (-1) 0) v := by
  have hx := C.exactAt_of_isGE 1 0 (by omega)
  rw [exactAt_iff' C (-1) 0 1 (by apply (ComplexShape.up ℤ).prev_eq'; rfl) (by apply (ComplexShape.up ℤ).next_eq'; rfl)] at hx
  have he : LinearMap.range (C.d (-1) 0).hom = LinearMap.ker (C.d 0 1).hom :=
    (ShortComplex.moduleCat_exact_iff_range_eq_ker _).mp hx
  rw [degreeMatrix_action]
  constructor
  · intro hv
    have hz : (C.d 0 1).hom ((c.equiv 0).symm v) = 0 :=
      (c.equiv 1).injective (hv.trans (map_zero _).symm)
    have hr : (c.equiv 0).symm v ∈ LinearMap.range (C.d (-1) 0).hom := by rw [he]; exact hz
    obtain ⟨w,hw⟩ := hr
    refine ⟨c.equiv (-1) w,?_⟩
    rw [degreeMatrix_action,LinearEquiv.symm_apply_apply,hw,LinearEquiv.apply_symm_apply]
  · rintro ⟨w,hw⟩
    rw [degreeMatrix_action] at hw
    have hv : (c.equiv 0).symm v = (C.d (-1) 0).hom ((c.equiv (-1)).symm w) := by
      rw [←hw,LinearEquiv.symm_apply_apply]
    rw [hv]
    have hz := C.d_comp_d (-1) 0 1
    have hzv := congrArg (fun f : C.X (-1) ⟶ C.X 1 => f ((c.equiv (-1)).symm w)) hz
    change (C.d 0 1).hom ((C.d (-1) 0).hom ((c.equiv (-1)).symm w)) = 0 at hzv
    rw [hzv,map_zero]

variable [DecidableEq K] {L h : ℕ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
variable (inp : Input (D := D) (L := L) (h := h) cC) (hDL : D ≤ L)
variable (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
  (g : StoredGamma cC inp hDL s t) (H : StoredHomotopy cC inp hDL s t g)
  (x : StoredExtraction cC inp hDL s t g H) (u : StoredStable cC inp hDL s t g H x)

theorem stable_original_dC : LaurentArithmetic.matrixDenote u.arrays.dC =
    AlgorithmTwoPhysicalTransport.identityChecksOrdinal (degreeMatrix cC 0 1) (stableExtraC cC inp hDL s t g H x) := by
  rw [u.correct]
  change LaurentArithmetic.matrixDenote (augmentedRelations (originalSelectors (L := L) cC)
    (nativeArrays cC inp hDL s t g H x).differentialC _ _) = _
  rw [augmentedRelations_correct _ _ _ (runBox_ge_input _ _ _ _ _)]
  rw [originalSlice_native cC cC (inputCoordinates (L := L) cC) (inputCoordinates (L := L) cC)
    _ _ (originalSelectors_realizes cC) (originalSelectors_realizes cC) 1 0 _ _
    (represents_at _ _ (nativeArrays_realizes cC inp hDL s t g H x).differentialC 0 1 rfl)]
  rfl

theorem stable_original_dT : LaurentArithmetic.matrixDenote u.arrays.dT =
    AlgorithmTwoPhysicalTransport.identityChecksOrdinal
      (degreeMatrix (originalFromFrame (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K)) 0 1)
      (stableExtraT cC inp hDL s t g H x) := by
  rw [u.correct]
  change LaurentArithmetic.matrixDenote (augmentedRelations
    (selectorsFromDegree (AlgorithmTwoToricData.degrees D s.multiplicities))
    (nativeArrays cC inp hDL s t g H x).differentialT _ _) = _
  rw [augmentedRelations_correct _ _ _ (runBox_ge_input _ _ _ _ _)]
  erw [originalSlice_native (originalFromFrame _) (originalFromFrame _)
    (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K) (AlgorithmTwoToricData.totalCoordinates D s.multiplicities K)
    _ _ (selectorsFromDegree_realizes _) (selectorsFromDegree_realizes _) 1 0 _ _
    (represents_at _ _ (nativeArrays_realizes cC inp hDL s t g H x).differentialT 0 1 rfl)]
  rfl

end
end Decoupling.HighDim.AlgorithmTwoPipeline
