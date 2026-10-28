import Decoupling.HighDim.GluedNativeMatrixMap
import Decoupling.HighDim.GluedNativeConeLayers

/-!
# Exactness of the concrete check-to-cone comparison

The only discarded coordinates form an actual exact augmentation kernel.
Surjectivity and this kernel calculation prove the positive native
quasi-isomorphism needed to identify the physical code's profile.
-/

namespace Decoupling.HighDim.Glued
open CategoryTheory CategoryTheory.Limits HomologicalComplex Koszul Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

theorem rightPlaquettes_surjective : Function.Surjective (rightPlaquettes K) := by
  intro z
  let u := coordinates (Laurent K 3) plaquetteEquiv z
  refine ⟨![0,0,0,u 0,u 1,u 2], ?_⟩
  apply (coordinates (Laurent K 3) plaquetteEquiv).injective
  rw [rightPlaquettes_coordinates]
  funext i
  fin_cases i <;> rfl

theorem rightConeComponent_zero_surjective : Function.Surjective (rightConeComponent K 0) :=
  (ModuleCat.epi_iff_surjective (coneCellIso K 2 (by decide)).hom).mp inferInstance |>.comp
    (rightPlaquettes_surjective K)

theorem rightConeComponent_two_bijective : Function.Bijective (rightConeComponent K 2) :=
  (coneCellIso K 0 (by decide)).toLinearEquiv.bijective.comp
    (coordinates (Laurent K 3) vertexEquiv).symm.bijective

@[reassoc] theorem rightConeComponent_one_cell :
    rightConeComponent K 1 ≫ coneCellProjection K 1 = -rightEdges K := by
  simp [rightConeComponent, Preadditive.add_comp, Preadditive.neg_comp, Category.assoc]

@[reassoc] theorem rightConeComponent_one_coefficient :
    rightConeComponent K 1 ≫ coneCoefficientProjection K = rightAugment K := by
  simp [rightConeComponent, Preadditive.add_comp, Preadditive.neg_comp, Category.assoc]

theorem rightConeComponent_one_surjective : Function.Surjective (rightConeComponent K 1) := by
  intro z
  let u := coordinates (Laurent K 3) edgeEquiv (coneCellProjection K 1 z)
  let a : K := coneCoefficientProjection K z
  let v : Fin 4 → Laurent K 3 := ![constant a, -u 0, -u 1, -u 2]
  have he : rightEdges K v = -coneCellProjection K 1 z := by
    apply (coordinates (Laurent K 3) edgeEquiv).injective
    rw [rightEdges_coordinates, map_neg]
    funext i
    fin_cases i <;> rfl
  have ha : rightAugment K v = coneCoefficientProjection K z := by
    change (show K from rightAugment K v) = a
    rw [rightAugment_apply]
    exact augmentation_constant a
  refine ⟨v, ?_⟩
  change (show (couplingCone K).X 1 from -(coneCellInclusion K 1 (rightEdges K v))) +
    coneCoefficientInclusion K (rightAugment K v) = z
  rw [he, ha, map_neg, neg_neg]
  exact coneOne_decomposition K z

/-- The actual kernel of the degree-one comparison consists of boundaries
of the displayed X-check matrix. -/
theorem rightConeComponent_one_kernel (v : (rightComplex K).X 1)
    (hv : rightConeComponent K 1 v = 0) : ∃ w, rightD K 0 w = v := by
  have he := congrArg (coneCellProjection K 1) hv
  change (rightConeComponent K 1 ≫ coneCellProjection K 1) v = _ at he
  rw [rightConeComponent_one_cell, map_zero] at he
  change -(rightEdges K v) = 0 at he
  have he0 := neg_eq_zero.mp he
  have ha := congrArg (coneCoefficientProjection K) hv
  change (rightConeComponent K 1 ≫ coneCoefficientProjection K) v = _ at ha
  rw [rightConeComponent_one_coefficient, map_zero] at ha
  have haug : augmentation (v (0 : Fin 4)) = 0 := by
    exact (rightAugment_apply K (show Fin 4 → Laurent K 3 from v)).symm.trans ha
  obtain ⟨u, hu⟩ := (laurent_exact_at_zero K 3
    (Finsupp.single vertex (v (0 : Fin 4)))).mp (by simpa using haug)
  let c := coordinates (Laurent K 3) edgeEquiv u
  have hc : firstBoundary (Laurent K 3) (difference K) *ᵥ c = ![v (0 : Fin 4)] := by
    rw [← firstBoundary_coordinates, ← boundary_coordinates K vertexEquiv edgeEquiv, hu]
    funext i
    fin_cases i
    simp [vertexEquiv]
  have hc0 := congrFun hc 0
  simp [firstBoundary, mulVec, dotProduct, Fin.sum_univ_succ] at hc0
  have hvv := congrArg (coordinates (Laurent K 3) edgeEquiv) he0
  rw [rightEdges_coordinates, map_zero] at hvv
  have hv1 := congrFun hvv 0
  have hv2 := congrFun hvv 1
  have hv3 := congrFun hvv 2
  refine ⟨![c 0,c 1,c 2,0,0,0], ?_⟩
  change xChecks K *ᵥ ![c 0,c 1,c 2,0,0,0] = v
  funext i
  fin_cases i
  · simpa [xChecks, mulVec, dotProduct, Fin.sum_univ_succ] using hc0
  · simpa [xChecks, mulVec, dotProduct, Fin.sum_univ_succ] using hv1.symm
  · simpa [xChecks, mulVec, dotProduct, Fin.sum_univ_succ] using hv2.symm
  · simpa [xChecks, mulVec, dotProduct, Fin.sum_univ_succ] using hv3.symm

end
end Decoupling.HighDim.Glued
