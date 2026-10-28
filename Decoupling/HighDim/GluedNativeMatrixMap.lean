import Decoupling.HighDim.GluedNativeComparison
import Decoupling.HighDim.GluedNativeConeCells
import Decoupling.HighDim.GluedNativeHomology

/-!
# The displayed checks map to the native gluing cone

The components are explicit: plaquettes in degree zero; minus the three
edge components and the augmented first vertex in degree one; the
vertex in degree two.
-/

namespace Decoupling.HighDim.Glued
open CategoryTheory CategoryTheory.Limits HomologicalComplex Koszul Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K]

def rightPlaquettes : resolutionTerm K 0 ⟶
    ModuleCat.of (Laurent K 3) (Term (Laurent K 3) 3 2) :=
  ModuleCat.ofHom (LinearMap.pi (fun i : Fin 3 => LinearMap.proj ((![3,4,5] : Fin 3 → Fin 6) i))) ≫
    (coordinates (Laurent K 3) plaquetteEquiv).toModuleIso.inv

def rightEdges : resolutionTerm K 1 ⟶
    ModuleCat.of (Laurent K 3) (Term (Laurent K 3) 3 1) :=
  ModuleCat.ofHom (LinearMap.pi (fun i : Fin 3 => LinearMap.proj ((![1,2,3] : Fin 3 → Fin 4) i))) ≫
    (coordinates (Laurent K 3) edgeEquiv).toModuleIso.inv

def rightVertex : resolutionTerm K 2 ⟶
    ModuleCat.of (Laurent K 3) (Term (Laurent K 3) 3 0) :=
  (coordinates (Laurent K 3) vertexEquiv).toModuleIso.inv

def rightAugment : resolutionTerm K 1 ⟶ coefficientModule K 3 :=
  ModuleCat.ofHom ((Finsupp.lsingle (R := Laurent K 3) vertex).comp (LinearMap.proj (0 : Fin 4))) ≫
    augmentationMap K 3

@[simp] theorem rightAugment_apply (v : Fin 4 → Laurent K 3) :
    (show K from rightAugment K v) = augmentation (v 0) := by
  change augmentation (zeroTermEquiv (Laurent K 3) (Finsupp.single vertex (v 0))) = _
  rw [zeroTermEquiv_single]

@[simp] theorem rightPlaquettes_coordinates (v : Fin 6 → Laurent K 3) :
    coordinates (Laurent K 3) plaquetteEquiv (rightPlaquettes K v) = ![v 3, v 4, v 5] := by
  change coordinates (Laurent K 3) plaquetteEquiv
    ((coordinates (Laurent K 3) plaquetteEquiv).symm (fun i => v (![3, 4, 5] i))) = _
  rw [LinearEquiv.apply_symm_apply]
  funext i
  fin_cases i <;> rfl

@[simp] theorem rightEdges_coordinates (v : Fin 4 → Laurent K 3) :
    coordinates (Laurent K 3) edgeEquiv (rightEdges K v) = ![v 1, v 2, v 3] := by
  change coordinates (Laurent K 3) edgeEquiv
    ((coordinates (Laurent K 3) edgeEquiv).symm (fun i => v (![1, 2, 3] i))) = _
  rw [LinearEquiv.apply_symm_apply]
  funext i
  fin_cases i <;> rfl

@[reassoc] theorem rightD_zero_edges :
    rightD K 0 ≫ rightEdges K =
      rightPlaquettes K ≫ boundary (Laurent K 3) (difference K) 1 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  apply (coordinates (Laurent K 3) edgeEquiv).injective
  change coordinates (Laurent K 3) edgeEquiv (rightEdges K (xChecks K *ᵥ v)) =
    coordinates (Laurent K 3) edgeEquiv
      (boundary (Laurent K 3) (difference K) 1 (rightPlaquettes K v))
  rw [rightEdges_coordinates, boundary_coordinates K edgeEquiv plaquetteEquiv,
    secondBoundary_coordinates, rightPlaquettes_coordinates]
  funext i
  fin_cases i <;> simp [xChecks, secondBoundary, mulVec, dotProduct, Fin.sum_univ_succ]

@[reassoc] theorem rightD_zero_augment :
    rightD K 0 ≫ rightAugment K = rightPlaquettes K ≫ couplingCochain K := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change (show K from rightAugment K (xChecks K *ᵥ v)) =
    (show K from couplingCochain K (rightPlaquettes K v))
  rw [rightAugment_apply, couplingCochain_apply]
  have hp := congrFun (rightPlaquettes_coordinates K v) 0
  change rightPlaquettes K v (plaquette 0) = v (3 : Fin 6) at hp
  rw [hp]
  simp [xChecks, mulVec, dotProduct, Fin.sum_univ_succ, map_add, map_mul]

@[reassoc] theorem rightD_one_vertex :
    rightD K 1 ≫ rightVertex K =
      rightEdges K ≫ boundary (Laurent K 3) (difference K) 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  apply (coordinates (Laurent K 3) vertexEquiv).injective
  change coordinates (Laurent K 3) vertexEquiv
    ((coordinates (Laurent K 3) vertexEquiv).symm (metacheck K *ᵥ v)) =
      coordinates (Laurent K 3) vertexEquiv
        (boundary (Laurent K 3) (difference K) 0 (rightEdges K v))
  rw [LinearEquiv.apply_symm_apply, boundary_coordinates K vertexEquiv edgeEquiv,
    firstBoundary_coordinates, rightEdges_coordinates]
  funext i
  fin_cases i
  simp [metacheck, firstBoundary, mulVec, dotProduct, Fin.sum_univ_succ]

/-- The explicit components of the native check-to-cone map. -/
def rightConeComponent : (n : ℕ) → (rightComplex K).X n ⟶ (couplingCone K).X (n : ℤ)
  | 0 => rightPlaquettes K ≫ coneCellInclusion K 2
  | 1 => (show resolutionTerm K 1 ⟶ (couplingCone K).X 1 from
      -(rightEdges K ≫ coneCellInclusion K 1)) +
      rightAugment K ≫ coneCoefficientInclusion K
  | 2 => rightVertex K ≫ coneCellInclusion K 0
  | _ + 3 => 0

theorem rightConeComponent_comm (n : ℕ) :
    rightConeComponent K n ≫ (couplingCone K).d (n : ℤ) ((n + 1 : ℕ) : ℤ) =
      (rightComplex K).d n (n + 1) ≫ rightConeComponent K (n + 1) := by
  rw [show (rightComplex K).d n (n + 1) = rightD K n from CochainComplex.of_d _ _ _]
  rcases n with _ | (_ | (_ | n))
  · change (rightPlaquettes K ≫ coneCellInclusion K 2) ≫ (couplingCone K).d 0 1 =
      rightD K 0 ≫ ((show resolutionTerm K 1 ⟶ (couplingCone K).X 1 from
      -(rightEdges K ≫ coneCellInclusion K 1)) +
        rightAugment K ≫ coneCoefficientInclusion K)
    rw [Category.assoc, coneCell_two_d]
    simp only [Preadditive.comp_add, Preadditive.comp_neg,
      rightD_zero_edges_assoc, rightD_zero_augment_assoc]
  · change ((show resolutionTerm K 1 ⟶ (couplingCone K).X 1 from
      -(rightEdges K ≫ coneCellInclusion K 1)) +
      rightAugment K ≫ coneCoefficientInclusion K) ≫ (couplingCone K).d 1 2 =
        rightD K 1 ≫ rightVertex K ≫ coneCellInclusion K 0
    simp only [Preadditive.add_comp, Preadditive.neg_comp, Category.assoc,
      coneCell_one_d, coneCoefficient_d, comp_zero, add_zero, Preadditive.comp_neg, neg_neg]
    rw [rightD_one_vertex_assoc]
  · exact (cone_X_zero K 3 (by omega)).eq_of_tgt _ _
  · exact (ModuleCat.isZero_of_subsingleton
      (R := Laurent K 3) (ModuleCat.of (Laurent K 3) (Fin 0 → Laurent K 3))).eq_of_src _ _

/-- The actual matrix check complex maps to the native cone of the
actual signed Ext representative. -/
def rightToCone : (rightComplex K).extend ComplexShape.embeddingUpNat ⟶ couplingCone K :=
  extendNatMap (rightComplex K) (couplingCone K) (rightConeComponent K)
    (rightConeComponent_comm K)

@[simp] theorem rightToCone_f (n : ℕ) :
    (rightToCone K).f (n : ℤ) =
      ((rightComplex K).extendXIso ComplexShape.embeddingUpNat rfl).hom ≫ rightConeComponent K n :=
  extendNatComponent_eq _ _ _ n

end
end Decoupling.HighDim.Glued
