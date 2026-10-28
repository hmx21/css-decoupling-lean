import Decoupling.HighDim.HermannTransport

/-!
# Finite index changes for coefficient-comparison kernel systems

The coefficient-comparison matrix has product index types. This file
transports the actual equations and polynomial span through their finite
enumerations, so induction for Fin-indexed matrices applies without a new
kernel-generation assumption.
-/

namespace Decoupling.HighDim.Hermann

open Matrix MvPolynomial EffectiveLinear
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [CommRing K] {N : ℕ}
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Enumerate the actual row and column sets without changing matrix entries. -/
def finiteMatrix (A : Matrix ι κ (MvPolynomial (Fin N) K)) :
    Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card κ)) (MvPolynomial (Fin N) K) :=
  A.submatrix (Fintype.equivFin ι).symm (Fintype.equivFin κ).symm

theorem finiteMatrix_kernel_iff (A : Matrix ι κ (MvPolynomial (Fin N) K))
    (y : Fin (Fintype.card κ) → MvPolynomial (Fin N) K) :
    finiteMatrix A *ᵥ y = 0 ↔ A *ᵥ (y ∘ Fintype.equivFin κ) = 0 := by
  rw [finiteMatrix, Matrix.submatrix_mulVec_equiv]
  constructor
  · intro h
    funext i
    have hi := congrFun h (Fintype.equivFin ι i)
    simpa only [Function.comp_apply, Equiv.symm_symm, Equiv.symm_apply_apply, Pi.zero_apply] using hi
  · intro h
    rw [show (Fintype.equivFin κ).symm.symm = Fintype.equivFin κ from rfl, h]
    rfl

/-- Pull a bounded generation theorem back through the finite column
permutation, transporting its actual span rather than only its dimension. -/
theorem finiteMatrix_kernel_mem_span (A : Matrix ι κ (MvPolynomial (Fin N) K)) (B : ℕ)
    (hgen : LinearMap.ker (finiteMatrix A).mulVecLin =
      Submodule.span (MvPolynomial (Fin N) K) (degreeKernel (finiteMatrix A) B))
    (y : κ → MvPolynomial (Fin N) K) (hy : A *ᵥ y = 0) :
    y ∈ Submodule.span (MvPolynomial (Fin N) K)
      {z : κ → MvPolynomial (Fin N) K | A *ᵥ z = 0 ∧ ∀ j, (z j).totalDegree ≤ B} := by
  classical
  let z := y ∘ (Fintype.equivFin κ).symm
  let L := LinearMap.funLeft (MvPolynomial (Fin N) K) (MvPolynomial (Fin N) K)
    (Fintype.equivFin κ)
  have hz : z ∈ Submodule.span (MvPolynomial (Fin N) K) (degreeKernel (finiteMatrix A) B) := by
    rw [← hgen]
    apply (finiteMatrix_kernel_iff A z).mpr
    simpa only [z, Function.comp_def, Equiv.symm_apply_apply] using hy
  have hL : L z = y := by
    funext j
    exact congrArg y ((Fintype.equivFin κ).symm_apply_apply j)
  rw [← hL]
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hz
  · intro x hx
    apply Submodule.subset_span
    exact ⟨(finiteMatrix_kernel_iff A x).mp hx.1, fun j => hx.2 _⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x z hx hz ihx ihz
    rw [map_add]
    exact Submodule.add_mem _ ihx ihz
  · intro a x hx ihx
    rw [map_smul]
    exact Submodule.smul_mem _ a ihx

end
end Decoupling.HighDim.Hermann
