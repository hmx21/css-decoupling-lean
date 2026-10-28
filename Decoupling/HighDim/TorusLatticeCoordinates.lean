import Decoupling.HighDim.TorusWindow
import Decoupling.HighDim.ScalingLatticeChecksProfile

/-!
# Finite-period coordinates in an arbitrary lattice basis

The quotient group-algebra coefficients agree with augmentation of the
actual coset-basis coordinates. Thus imposing periods is exactly imposing
augmentation after physical lattice restriction, including skew lattices.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits LatticeRestriction ScalingLattice Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

variable (K : Type) [Field K] {D : ℕ}
  (L : AddSubgroup (Translation D)) [L.FiniteIndex] (e : L ≃+ Translation D)

omit [L.FiniteIndex] in
theorem periodMap_coordinateEmbedding (a : Laurent K D) :
    periodMap L (coordinateEmbedding K L e a) = periodConstant L (augmentation a) := by
  have he : (periodMap (K := K) L).comp (coordinateEmbedding K L e) =
      (periodConstant L).comp (augmentation : Laurent K D →+* K) := by
    apply AddMonoidAlgebra.ringHom_ext
    · intro c
      simp [periodMap, periodConstant, coordinateEmbedding_single]
    · intro a
      change periodMap L (coordinateEmbedding K L e (monomial K a)) =
        periodConstant L (augmentation (monomial K a))
      rw [coordinateEmbedding_monomial, periodMap_period _ _ (e.symm a).property,
        augmentation_monomial, map_one]
  exact DFunLike.congr_fun he a

omit [L.FiniteIndex] in
theorem periodMap_retained (a : S K L) :
    periodMap L (a : Laurent K D) = periodConstant L
      (augmentation (ringCoordinates K L e a)) := by
  have h := periodMap_coordinateEmbedding K L e (ringCoordinates K L e a)
  change periodMap L (((ringCoordinates K L e).symm (ringCoordinates K L e a)) : Laurent K D) =
    periodConstant L (augmentation (ringCoordinates K L e a)) at h
  simpa only [RingEquiv.symm_apply_apply] using h

theorem periodMap_coeff (a : Laurent K D) (p : Coset L) :
    (periodMap L a).coeff p =
      augmentation (ringCoordinates K L e ((cosetBasis K L).repr a p)) := by
  classical
  conv_lhs => rw [← (cosetBasis K L).sum_repr a]
  simp only [map_sum]
  have hs (q : Coset L) :
      periodMap L ((cosetBasis K L).repr a q • cosetBasis K L q) =
        AddMonoidAlgebra.single q
          (augmentation (ringCoordinates K L e ((cosetBasis K L).repr a q))) := by
    change periodMap L (((cosetBasis K L).repr a q : Laurent K D) * cosetBasis K L q) = _
    rw [map_mul, periodMap_retained K L e, cosetBasis_apply, periodMap_monomial,
      representative_class]
    simp [periodConstant]
  simp_rw [hs]
  simp [Finsupp.single_apply]

/-- Coefficient coordinates of the true finite-period group algebra. -/
def periodCoordinates : PeriodRing K L ≃ₗ[K] (Coset L → K) :=
  (AddMonoidAlgebra.basis (Coset L) K).equivFun

@[simp] theorem periodCoordinates_apply (a : PeriodRing K L) (p : Coset L) :
    periodCoordinates K L a p = a.coeff p := rfl

/-- Every multiplication-matrix entry descends to the actual periodic
convolution coefficient. -/
theorem periodMul_basis (a : Laurent K D) (p q : Coset L) :
    (periodMap L a * AddMonoidAlgebra.single q 1).coeff p =
      augmentation (ringCoordinates K L e (LatticePhysical.expandScalar K L a p q)) := by
  classical
  have hb : AddMonoidAlgebra.single q 1 = periodMap L (cosetBasis K L q) := by
    rw [cosetBasis_apply, periodMap_monomial, representative_class]
  rw [hb, ← map_mul, periodMap_coeff K L e]
  rw [LatticePhysical.expandScalar, Algebra.leftMulMatrix_eq_repr_mul]

theorem periodMul_coordinates (a : Laurent K D) (v : PeriodRing K L) (p : Coset L) :
    (periodMap L a * v).coeff p = ∑ q,
      augmentation (ringCoordinates K L e (LatticePhysical.expandScalar K L a p q)) *
        v.coeff q := by
  conv_lhs => rw [← (AddMonoidAlgebra.basis (Coset L) K).sum_repr v]
  simp only [Finset.mul_sum, mul_smul_comm, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro q _
  rw [AddMonoidAlgebra.basis_apply, periodMul_basis K L e]
  change v.coeff q * _ = _ * v.coeff q
  exact mul_comm _ _

/-- Periodic qudits are the residue-cell coordinates of one coarse cell. -/
def periodicVectorCoordinates (n : ℕ) :
    (Fin n → PeriodRing K L) ≃ₗ[K] (Fin (count L n) → K) where
  toFun v i := (v ((Fintype.equivFin (Fin n × Coset L)).symm i).1).coeff
    ((Fintype.equivFin (Fin n × Coset L)).symm i).2
  invFun v i := (periodCoordinates K L).symm (fun p => v (Fintype.equivFin _ (i, p)))
  left_inv v := by
    funext i
    dsimp
    simp only [Equiv.symm_apply_apply]
    exact (periodCoordinates K L).symm_apply_apply (v i)
  right_inv v := by
    funext i
    dsimp
    rw [← periodCoordinates_apply, LinearEquiv.apply_symm_apply]
    simp
  map_add' v w := by funext i; simp
  map_smul' a v := by funext i; simp

theorem periodicVectorCoordinates_naturality {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (Laurent K D)) (v : Fin n → PeriodRing K L) :
    periodicVectorCoordinates K L m ((A.map (periodMap L)) *ᵥ v) =
      ((physicalMatrix K L e A).map augmentation) *ᵥ periodicVectorCoordinates K L n v := by
  classical
  funext i
  let p := ((Fintype.equivFin (Fin m × Coset L)).symm i).2
  let j := ((Fintype.equivFin (Fin m × Coset L)).symm i).1
  change (∑ k : Fin n, periodMap L (A j k) * v k).coeff p = _
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  simp_rw [periodMul_coordinates K L e]
  change (∑ k : Fin n, ∑ q : Coset L,
      augmentation (ringCoordinates K L e (LatticePhysical.expandScalar K L (A j k) p q)) *
        (v k).coeff q) =
    ∑ k : Fin (count L n), augmentation
      (ringCoordinates K L e (LatticePhysical.expandScalar K L
        (A j ((Fintype.equivFin (Fin n × Coset L)).symm k).1) p
          ((Fintype.equivFin (Fin n × Coset L)).symm k).2)) *
      (v ((Fintype.equivFin (Fin n × Coset L)).symm k).1).coeff
        ((Fintype.equivFin (Fin n × Coset L)).symm k).2
  let f : Fin n × Coset L → K := fun k =>
    augmentation (ringCoordinates K L e (LatticePhysical.expandScalar K L (A j k.1) p k.2)) *
      (v k.1).coeff k.2
  exact (Fintype.sum_prod_type f).symm.trans
    (Fintype.sum_equiv (Fintype.equivFin (Fin n × Coset L)).symm
      (fun k => f ((Fintype.equivFin (Fin n × Coset L)).symm k)) f (fun _ => rfl)).symm

end
end Decoupling.HighDim.Torus
