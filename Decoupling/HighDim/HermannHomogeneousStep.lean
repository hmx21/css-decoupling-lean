import Decoupling.HighDim.HermannTransportFinite
import Decoupling.HighDim.HermannMonicDivision
import Decoupling.HighDim.HermannMatrixReduction
import Decoupling.HighDim.HermannCoefficientDegree

/-!
# Lifting lower-variable kernel generators through actual coefficient comparison

This is the genuine induction step after monic-minor normalization. Every
last-variable-bounded solution is decoded into the actual coefficient
matrix kernel. Its lower-variable generators are reassembled as actual
solutions, with the proved total-degree bound.
-/

namespace Decoupling.HighDim.Hermann
open Matrix MvPolynomial EffectiveLinear
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {N m n : ℕ}

@[simp] theorem lastEncode_zero {R : Type*} [CommRing R] (b : ℕ) :
    lastEncode (n := n) b (0 : (Fin n × Fin b) → R) = 0 := by
  funext j
  change (((Polynomial.degreeLTEquiv R b).symm 0).val) = 0
  rw [map_zero]
  rfl

theorem lastEncode_add {R : Type*} [CommRing R] (b : ℕ)
    (x y : (Fin n × Fin b) → R) : lastEncode b (x+y) = lastEncode b x + lastEncode b y := by
  funext j
  exact congrArg Subtype.val ((Polynomial.degreeLTEquiv R b).symm.map_add
    (fun k => x (j,k)) (fun k => y (j,k)))

theorem lastEncode_smul {R : Type*} [CommRing R] (b : ℕ)
    (a : R) (x : (Fin n × Fin b) → R) :
    lastEncode b (a • x) = Polynomial.C a • lastEncode b x := by
  funext j
  have h := congrArg Subtype.val ((Polynomial.degreeLTEquiv R b).symm.map_smul
    a (fun k => x (j,k)))
  simpa only [lastEncode, Submodule.coe_smul, Polynomial.smul_eq_C_mul,
    Pi.smul_apply, Pi.smul_def, smul_eq_mul] using h

theorem natDegree_le_flatten_totalDegree (P : Polynomial (MvPolynomial (Fin N) K)) :
    P.natDegree ≤ (flatten P).totalDegree := by
  have h := degreeOf_le_totalDegree (flatten P) 0
  rw [← natDegree_finSuccEquiv, AlgEquiv.apply_symm_apply] at h
  exact h

/-- Coefficient-kernel vectors reassemble to actual polynomial-kernel vectors. -/
theorem lastEncode_kernel (A : Matrix (Fin m) (Fin n) (Polynomial (MvPolynomial (Fin N) K)))
    (d b : ℕ) (hA : ∀ i j, (A i j).natDegree ≤ d)
    (x : (Fin n × Fin b) → MvPolynomial (Fin N) K)
    (hx : lastCoefficientMatrix A d b *ᵥ x = 0) : A *ᵥ lastEncode b x = 0 := by
  have h := lastCoefficientMatrix_mulVec A d b x
  rw [hx] at h
  have he := congrArg (lastEncode (d+b)) h.symm
  rw [lastEncode_decode _ _ (mulVec_degree_lt A d b hA _ (lastEncode_degree b x)),
    lastEncode_zero] at he
  exact he

/-- A lower-variable generation theorem implies the required membership for
all actual solutions satisfying the strict last-variable cutoff. -/
theorem smallLastKernel_flatten_mem_span
    (A : Matrix (Fin m) (Fin n) (Polynomial (MvPolynomial (Fin N) K)))
    (d b B : ℕ) (hA : ∀ i j, (A i j).natDegree ≤ d)
    (hgen : LinearMap.ker (finiteMatrix (lastCoefficientMatrix A d b)).mulVecLin =
      Submodule.span (MvPolynomial (Fin N) K)
        (degreeKernel (finiteMatrix (lastCoefficientMatrix A d b)) B))
    (y : Fin n → Polynomial (MvPolynomial (Fin N) K)) (hy : y ∈ smallLastKernel A b) :
    mapVector flatten y ∈ Submodule.span (MvPolynomial (Fin (N+1)) K)
      (degreeKernel (A.map flatten) (B+b)) := by
  let z := lastDecode b y
  have hz : lastCoefficientMatrix A d b *ᵥ z = 0 := by
    rw [lastCoefficientMatrix_mulVec, lastEncode_decode b y hy.2, hy.1]
    funext j
    simp [lastDecode]
  have hs := finiteMatrix_kernel_mem_span (lastCoefficientMatrix A d b) B hgen z hz
  have hspan : ∀ x, x ∈ Submodule.span (MvPolynomial (Fin N) K)
      {x : (Fin n × Fin b) → MvPolynomial (Fin N) K |
        lastCoefficientMatrix A d b *ᵥ x = 0 ∧ ∀ j, (x j).totalDegree ≤ B} →
      mapVector flatten (lastEncode b x) ∈ Submodule.span (MvPolynomial (Fin (N+1)) K)
        (degreeKernel (A.map flatten) (B+b)) := by
    intro x hx
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hx
    · intro w hw
      apply Submodule.subset_span
      constructor
      · exact (mapVector_kernel_iff flatten.toRingEquiv A (lastEncode b w)).mpr
          (lastEncode_kernel A d b hA w hw.1)
      · intro j
        exact (lastEncode_totalDegree_le b B w hw.2 j).trans
          (Nat.add_le_add_left (Nat.sub_le b 1) B)
    · rw [lastEncode_zero]
      have he : mapVector flatten (0 : Fin n → Polynomial (MvPolynomial (Fin N) K)) = 0 := by
        funext j
        exact map_zero flatten
      rw [he]
      exact Submodule.zero_mem _
    · intro w z hw hz ihw ihz
      rw [lastEncode_add]
      have he : mapVector flatten (lastEncode b w + lastEncode b z) =
          mapVector flatten (lastEncode b w) + mapVector flatten (lastEncode b z) := by
        funext j
        exact map_add flatten _ _
      rw [he]
      exact Submodule.add_mem _ ihw ihz
    · intro a w hw ihw
      rw [lastEncode_smul]
      have he : mapVector flatten (Polynomial.C a • lastEncode b w) =
          flatten (Polynomial.C a) • mapVector flatten (lastEncode b w) := by
        funext j
        exact map_mul flatten _ _
      rw [he]
      exact Submodule.smul_mem _ _ ihw
  have h := hspan z hs
  rwa [lastEncode_decode b y hy.2] at h

/-- One true Hermann kernel-generation step with a proved lower-variable
input. The full theorem will discharge that input by induction on N. -/
theorem normalized_kernel_generation
    (A : Matrix (Fin m) (Fin n) (Polynomial (MvPolynomial (Fin N) K)))
    (δ : Polynomial (MvPolynomial (Fin N) K)) (hδ : δ.Monic)
    (E : Matrix (Fin n) (Fin n) (Polynomial (MvPolynomial (Fin N) K)))
    (hAE : A*E=0) (hEker : ∀ y, A *ᵥ y = 0 → E *ᵥ y = δ • y)
    (d M B : ℕ) (hA : ∀ i j, (A i j).natDegree ≤ d)
    (hE : ∀ i j, (flatten (E i j)).totalDegree ≤ M)
    (hgen : LinearMap.ker (finiteMatrix (lastCoefficientMatrix A d M)).mulVecLin =
      Submodule.span (MvPolynomial (Fin N) K)
        (degreeKernel (finiteMatrix (lastCoefficientMatrix A d M)) B)) :
    LinearMap.ker (A.map flatten).mulVecLin =
      Submodule.span (MvPolynomial (Fin (N+1)) K) (degreeKernel (A.map flatten) (B+M)) := by
  have hnative := kernel_eq_span_columns_small δ hδ A E hAE hEker M
    (fun i j => (natDegree_le_flatten_totalDegree (E i j)).trans (hE i j))
  apply le_antisymm
  · intro y hy
    change A.map flatten *ᵥ y = 0 at hy
    let z := mapVector (finSuccEquiv K N) y
    have hz : A *ᵥ z = 0 := by
      apply (mapVector_kernel_iff flatten.toRingEquiv A z).mp
      change A.map flatten *ᵥ (fun j => flatten (finSuccEquiv K N (y j))) = 0
      simpa only [AlgEquiv.symm_apply_apply] using hy
    have hmem : z ∈ Submodule.span (Polynomial (MvPolynomial (Fin N) K))
        (Set.range E.col ∪ smallLastKernel A M) := by
      rw [← hnative]
      exact hz
    have h := mapVector_span_mem flatten.toRingHom
      (Set.range E.col ∪ smallLastKernel A M)
      (Submodule.span (MvPolynomial (Fin (N+1)) K) (degreeKernel (A.map flatten) (B+M)))
      (fun w hw => ?_) z hmem
    · have he : mapVector flatten.toRingHom z = y := by
        funext j
        exact (finSuccEquiv K N).symm_apply_apply (y j)
      rwa [he] at h
    · rcases hw with ⟨j,rfl⟩ | hw
      · apply Submodule.subset_span
        constructor
        · apply (mapVector_kernel_iff flatten.toRingEquiv A (E.col j)).mpr
          funext i
          exact congrArg (fun F => F i j) hAE
        · intro i
          exact (hE i j).trans (Nat.le_add_left _ _)
      · exact smallLastKernel_flatten_mem_span A d M B hA hgen w hw
  · exact Submodule.span_le.mpr (fun _ hy => hy.1)

end
end Decoupling.HighDim.Hermann
