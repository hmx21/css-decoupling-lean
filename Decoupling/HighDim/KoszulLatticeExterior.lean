import Decoupling.HighDim.KoszulLatticePaths
import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction

/-!
# Exterior realization of the signed Koszul differential

Source: Appendix B.2, exterior product and its Leibniz differential.
The contraction is the proved mathlib Clifford/exterior contraction. Its
coordinates are related below to the actual existing Koszul cell complex.
-/

namespace Decoupling.HighDim.KoszulLattice

open Koszul ExtValues
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R]
variable {M : Type*} [AddCommGroup M] [Module R M]

/-- The full signed contraction formula, with no characteristic restriction. -/
theorem contract_ιMulti (d : Module.Dual R M) (n : ℕ) (v : Fin (n + 1) → M) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) d
      (ExteriorAlgebra.ιMulti R (n + 1) v) =
      ∑ i : Fin (n + 1), ((-1 : R) ^ i.val * d (v i)) •
        ExteriorAlgebra.ιMulti R n (fun j => v (i.succAbove j)) := by
  induction n with
  | zero =>
    conv_rhs => rw [Fin.sum_univ_succ]
    simp [ExteriorAlgebra.ιMulti_succ_apply, ExteriorAlgebra.ιMulti_zero_apply,
      CliffordAlgebra.contractLeft_ι, Algebra.algebraMap_eq_smul_one]
  | succ n ih =>
    conv_rhs => rw [Fin.sum_univ_succ]
    rw [ExteriorAlgebra.ιMulti_succ_apply, CliffordAlgebra.contractLeft_ι_mul,
      ih]
    simp only [Fin.val_zero, pow_zero, one_mul, Fin.succAbove_zero,
      Matrix.vecTail, Fin.val_succ, pow_succ, mul_neg_one, neg_mul,
      neg_smul, Finset.sum_neg_distrib, Finset.mul_sum, mul_smul_comm]
    rw [← sub_eq_add_neg]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [ExteriorAlgebra.ιMulti_succ_apply]
    congr 2
    simp [Matrix.vecTail, Function.comp_def]

/-- Contraction is natural for an actual linear map, with the dual form
pulled back on the source. -/
theorem contract_map {N : Type*} [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (d : Module.Dual R N) (x : ExteriorAlgebra R M) :
    CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R N)) d (ExteriorAlgebra.map f x) =
      ExteriorAlgebra.map f
        (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R M)) (d.comp f) x) := by
  induction x using CliffordAlgebra.left_induction with
  | algebraMap r => simp [CliffordAlgebra.contractLeft_algebraMap]
  | add x y hx hy => simp [hx, hy]
  | ι_mul m x hx =>
    simp only [map_mul, ExteriorAlgebra.map_apply_ι, CliffordAlgebra.contractLeft_ι_mul,
      LinearMap.comp_apply, map_sub, map_smul, hx]

variable (R) (D : ℕ)

/-- The existing ordered-cell term as the genuine exterior power. -/
def termExteriorEquiv (n : ℕ) : Term R D n ≃ₗ[R] (⋀[R]^n (Fin D → R)) :=
  (exteriorCellBasis R D n).repr.symm

/-- Embed one homogeneous Koszul term in the exterior algebra. -/
def termExterior (n : ℕ) : Term R D n →ₗ[R] ExteriorAlgebra R (Fin D → R) :=
  (ExteriorAlgebra.exteriorPower R n (Fin D → R)).subtype.comp
    (termExteriorEquiv R D n).toLinearMap

theorem termExterior_injective (n : ℕ) : Function.Injective (termExterior R D n) :=
  Subtype.val_injective.comp (termExteriorEquiv R D n).injective

@[simp] theorem termExterior_single (n : ℕ) (I : Cell D n) (r : R) :
    termExterior R D n (Finsupp.single I r) =
      r • ExteriorAlgebra.ιMulti R n (fun i => Pi.single (I i) 1) := by
  change ((exteriorCellBasis R D n).repr.symm (Finsupp.single I r) :
    ExteriorAlgebra R (Fin D → R)) = _
  rw [Module.Basis.repr_symm_single, exteriorCellBasis_apply]
  rfl

/-- The covector whose values on the coordinate vectors are the Koszul
weights. -/
def weightForm (w : Fin D → R) : Module.Dual R (Fin D → R) :=
  (Pi.basisFun R (Fin D)).constr R w

@[simp] theorem weightForm_single (w : Fin D → R) (i : Fin D) :
    weightForm R D w (Pi.single i 1) = w i := by
  rw [← Pi.basisFun_apply]
  exact (Pi.basisFun R (Fin D)).constr_basis R w i

/-- The actual signed Koszul boundary is exactly exterior contraction. -/
theorem termExterior_boundary (w : Fin D → R) (n : ℕ) (x : Term R D (n + 1)) :
    termExterior R D n (boundary R w n x) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin D → R)))
        (weightForm R D w) (termExterior R D (n + 1) x) := by
  have h : (termExterior R D n).comp (boundary R w n).hom =
      (CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin D → R)))
        (weightForm R D w)).comp (termExterior R D (n + 1)) := by
    apply (Finsupp.basisSingleOne : Module.Basis (Cell D (n + 1)) R
      (Term R D (n + 1))).ext
    intro I
    change termExterior R D n (boundary R w n (Finsupp.single I 1)) =
      CliffordAlgebra.contractLeft (Q := (0 : QuadraticForm R (Fin D → R)))
        (weightForm R D w) (termExterior R D (n + 1) (Finsupp.single I 1))
    rw [boundary_basis, map_sum, termExterior_single, one_smul, contract_ιMulti]
    apply Finset.sum_congr rfl
    intro i _
    rw [termExterior_single, weightForm_single]
    rfl
  exact LinearMap.congr_fun h x

end
end Decoupling.HighDim.KoszulLattice
