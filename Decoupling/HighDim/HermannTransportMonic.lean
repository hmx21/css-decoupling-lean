import Decoupling.HighDim.HermannTransport
import Decoupling.HighDim.HermannMonicDivision
import Decoupling.HighDim.HermannRank
import Decoupling.HighDim.HermannSyzygyMatrix

/-!
# Actual maximal-minor and monic coordinate normalization

The data is constructed from an actual nonzero minor, its adjugate, and the
proved degree-preserving linear coordinate change. It retains the explicit
lift H with A H = δ I and E = δ I - H A, needed by both homogeneous and
inhomogeneous Hermann induction.
-/

namespace Decoupling.HighDim.Hermann

open Matrix MvPolynomial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
variable {K : Type*} [Field K] {N r m n : ℕ}

/-- The adjugate lift using the actual selected columns. -/
def minorAdjugateLift {S : Type*} [CommRing S]
    (A : Matrix (Fin r) (Fin n) S) (cols : Fin r ↪ Fin n) :=
  columnInclusion cols * (A.submatrix id cols).adjugate

theorem mul_minorAdjugateLift {S : Type*} [CommRing S]
    (A : Matrix (Fin r) (Fin n) S) (cols : Fin r ↪ Fin n) :
    A * minorAdjugateLift A cols = (A.submatrix id cols).det • 1 := by
  rw [minorAdjugateLift, ← Matrix.mul_assoc, mul_columnInclusion, Matrix.mul_adjugate]

theorem minorAdjugateLift_totalDegree_le
    (A : Matrix (Fin r) (Fin n) (MvPolynomial (Fin (N+1)) K))
    (cols : Fin r ↪ Fin n) (d : ℕ) (hA : ∀ i j, (A i j).totalDegree ≤ d)
    (i : Fin n) (j : Fin r) : (minorAdjugateLift A cols i j).totalDegree ≤ r*d := by
  classical
  have hAdj (k j : Fin r) : ((A.submatrix id cols).adjugate k j).totalDegree ≤ r*d := by
    have h := adjugate_mul_totalDegree_le (A.submatrix id cols)
      (1 : Matrix (Fin r) (Fin r) (MvPolynomial (Fin (N+1)) K)) d
      (fun i j => hA i (cols j))
      (by
        intro i j
        by_cases hij : i=j
        · subst j
          simpa only [Matrix.one_apply_eq, totalDegree_one] using Nat.zero_le d
        · simpa only [Matrix.one_apply_ne hij, totalDegree_zero] using Nat.zero_le d) k j
    simpa only [Matrix.mul_one] using h
  change (∑ k, columnInclusion cols i k * (A.submatrix id cols).adjugate k j).totalDegree ≤ _
  apply totalDegree_finsetSum_le
  intro k _
  unfold columnInclusion
  split
  · simpa only [one_mul] using hAdj k j
  · simp

/-- Compose the linear variable change with the distinguished-variable equivalence. -/
def polynomialCoordinates
    (e : MvPolynomial (Fin (N+1)) K ≃ₐ[K] MvPolynomial (Fin (N+1)) K) :
    MvPolynomial (Fin (N+1)) K ≃ₐ[K] Polynomial (MvPolynomial (Fin N) K) :=
  e.trans (finSuccEquiv K N)

def transformedMatrix
    (e : MvPolynomial (Fin (N+1)) K ≃ₐ[K] MvPolynomial (Fin (N+1)) K)
    (A : Matrix (Fin r) (Fin n) (MvPolynomial (Fin (N+1)) K)) :=
  A.map (polynomialCoordinates e)

theorem totalDegree_C_unit_mul {σ : Type*} (u : Kˣ) (P : MvPolynomial σ K) :
    (C (u : K) * P).totalDegree = P.totalDegree := by
  apply le_antisymm
  · exact (totalDegree_mul _ _).trans (by simp)
  · have hi : C ((u⁻¹ : Kˣ) : K) * (C (u : K) * P) = P := by
      rw [← mul_assoc, ← map_mul]
      simp
    have h := totalDegree_mul (C ((u⁻¹ : Kˣ) : K)) (C (u : K) * P)
    rw [hi, totalDegree_C, zero_add] at h
    exact h

private theorem map_scalar_one {S T : Type*} [CommRing S] [CommRing T]
    (φ : S →+* T) (a : S) :
    (a • (1 : Matrix (Fin r) (Fin r) S)).map φ = φ a • 1 := by
  classical
  ext i j
  by_cases h : i=j <;> simp [Matrix.map_apply, Matrix.smul_apply, h]

private theorem scale_right_inverse {S : Type*} [CommRing S]
    (A : Matrix (Fin r) (Fin n) S) (H : Matrix (Fin n) (Fin r) S)
    (δ s : S) (h : A*H=δ • 1) : A*(s • H)=(s*δ) • 1 := by
  rw [Matrix.mul_smul, h, smul_smul]

private theorem scale_mapped_syzygy {S T : Type*} [CommRing S] [CommRing T]
    (φ : S →+* T) (A : Matrix (Fin r) (Fin n) S)
    (H : Matrix (Fin n) (Fin r) S) (E : Matrix (Fin n) (Fin n) S)
    (δ : S) (s : T) (hE : E=δ • 1-H*A) :
    s • E.map φ = (s*φ δ) • 1 - (s • H.map φ)*A.map φ := by
  rw [hE, Matrix.map_sub, smul_sub, map_scalar_one, smul_smul,
    Matrix.smul_mul, ← Matrix.map_mul]
  exact map_sub φ

/-- All data needed for one-variable elimination of an actual full-row minor. -/
structure MonicMinorData
    (A : Matrix (Fin r) (Fin n) (MvPolynomial (Fin (N+1)) K)) (d : ℕ) where
  e : MvPolynomial (Fin (N+1)) K ≃ₐ[K] MvPolynomial (Fin (N+1)) K
  preservesDegree : ∀ P, (e P).totalDegree = P.totalDegree
  δ : Polynomial (MvPolynomial (Fin N) K)
  monic : δ.Monic
  divisorDegree : (flatten δ).totalDegree = δ.natDegree
  H : Matrix (Fin n) (Fin r) (Polynomial (MvPolynomial (Fin N) K))
  E : Matrix (Fin n) (Fin n) (Polynomial (MvPolynomial (Fin N) K))
  mul_H : transformedMatrix e A * H = δ • 1
  E_eq : E = δ • 1 - H * transformedMatrix e A
  matrixDegree : ∀ i j, (flatten (transformedMatrix e A i j)).totalDegree ≤ d
  HDegree : ∀ i j, (flatten (H i j)).totalDegree ≤ r*d
  EDegree : ∀ i j, (flatten (E i j)).totalDegree ≤ r*d

private theorem mul_syzygy_of_lift {S : Type*} [CommRing S]
    (A : Matrix (Fin r) (Fin n) S) (H : Matrix (Fin n) (Fin r) S)
    (E : Matrix (Fin n) (Fin n) S) (δ : S)
    (hAH : A*H=δ • 1) (hE : E=δ • 1-H*A) : A*E=0 := by
  rw [hE, Matrix.mul_sub, Matrix.mul_smul, Matrix.mul_one,
    ← Matrix.mul_assoc, hAH, Matrix.smul_mul, Matrix.one_mul, sub_self]

private theorem syzygy_kernel_of_lift {S : Type*} [CommRing S]
    (A : Matrix (Fin r) (Fin n) S) (H : Matrix (Fin n) (Fin r) S)
    (E : Matrix (Fin n) (Fin n) S) (δ : S) (hE : E=δ • 1-H*A)
    (y : Fin n → S) (hy : A *ᵥ y=0) : E *ᵥ y=δ • y := by
  rw [hE, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    ← Matrix.mulVec_mulVec, hy, Matrix.mulVec_zero, sub_zero]

namespace MonicMinorData
variable {A : Matrix (Fin r) (Fin n) (MvPolynomial (Fin (N+1)) K)} {d : ℕ}
  (M : MonicMinorData A d)

theorem mul_E : transformedMatrix M.e A * M.E = 0 :=
  mul_syzygy_of_lift _ _ _ _ M.mul_H M.E_eq

theorem E_kernel (y : Fin n → Polynomial (MvPolynomial (Fin N) K))
    (hy : transformedMatrix M.e A *ᵥ y = 0) : M.E *ᵥ y = M.δ • y :=
  syzygy_kernel_of_lift _ _ _ _ M.E_eq y hy

end MonicMinorData

/-- Construction from the selected actual minor; no normalized data is an input. -/
def monicMinorData [Infinite K]
    (A : Matrix (Fin r) (Fin n) (MvPolynomial (Fin (N+1)) K))
    (cols : Fin r ↪ Fin n) (hdet : (A.submatrix id cols).det ≠ 0)
    (d : ℕ) (hA : ∀ i j, (A i j).totalDegree ≤ d) : MonicMinorData A d := by
  classical
  apply Classical.choice
  obtain ⟨e,he,u,hu,hn⟩ := exists_linear_monic_coordinates N (A.submatrix id cols).det hdet
  let φ := (polynomialCoordinates e).toRingHom
  let s : Polynomial (MvPolynomial (Fin N) K) := Polynomial.C (C ((u⁻¹ : Kˣ) : K))
  let δ := s * φ (A.submatrix id cols).det
  let H := s • (minorAdjugateLift A cols).map φ
  let E := s • (syzygyMatrix A cols).map φ
  have hunit : IsUnit (C ((u⁻¹ : Kˣ) : K) : MvPolynomial (Fin N) K) :=
    (u⁻¹).isUnit.map C
  have hf (P : MvPolynomial (Fin (N+1)) K) :
      flatten (s * φ P) = C ((u⁻¹ : Kˣ) : K) * e P := by
    simp [s, φ, polynomialCoordinates, map_mul]
  have hδ : δ.Monic := by
    change (Polynomial.C (C ((u⁻¹ : Kˣ) : K)) * φ _).leadingCoeff = 1
    rw [Polynomial.leadingCoeff_C_mul_of_isUnit hunit]
    change C ((u⁻¹ : Kˣ) : K) * (finSuccEquiv K N (e _)).leadingCoeff = 1
    rw [hu, ← map_mul]
    simp
  have hδn : δ.natDegree = (A.submatrix id cols).det.totalDegree := by
    rw [show δ = Polynomial.C (C ((u⁻¹ : Kˣ) : K)) * φ _ from rfl,
      Polynomial.natDegree_C_mul_of_isUnit hunit]
    exact hn
  have hmap : (transformedMatrix e A) * (minorAdjugateLift A cols).map φ =
      φ (A.submatrix id cols).det • 1 := by
    change A.map φ * (minorAdjugateLift A cols).map φ = _
    rw [← Matrix.map_mul, mul_minorAdjugateLift, map_scalar_one]
  refine ⟨{
    e := e
    preservesDegree := he
    δ := δ
    monic := hδ
    divisorDegree := ?_
    H := H
    E := E
    mul_H := ?_
    E_eq := ?_
    matrixDegree := ?_
    HDegree := ?_
    EDegree := ?_
  }⟩
  · rw [hf, totalDegree_C_unit_mul, he, hδn]
  · exact scale_right_inverse (transformedMatrix e A) ((minorAdjugateLift A cols).map φ)
      (φ (A.submatrix id cols).det) s hmap
  · exact scale_mapped_syzygy φ A (minorAdjugateLift A cols)
      (syzygyMatrix A cols) (A.submatrix id cols).det s rfl
  · intro i j
    change (flatten (polynomialCoordinates e (A i j))).totalDegree ≤ d
    simpa only [flatten, polynomialCoordinates, AlgEquiv.trans_apply,
      AlgEquiv.symm_apply_apply, he] using hA i j
  · intro i j
    change (flatten (s * φ (minorAdjugateLift A cols i j))).totalDegree ≤ r*d
    rw [hf, totalDegree_C_unit_mul, he]
    exact minorAdjugateLift_totalDegree_le A cols d hA i j
  · intro i j
    change (flatten (s * φ (syzygyMatrix A cols i j))).totalDegree ≤ r*d
    rw [hf, totalDegree_C_unit_mul, he]
    exact syzygyMatrix_totalDegree_le A cols d hA i j

/-- Select the actual maximal minor and then normalize. All original kernel
equations are retained; no rank/minor/normalization certificate is supplied. -/
theorem exists_monicMinorData [Infinite K]
    (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin (N+1)) K))
    (d : ℕ) (hA : ∀ i j, (A i j).totalDegree ≤ d) :
    ∃ (r : ℕ) (rows : Fin r ↪ Fin m), r ≤ m ∧
      (∀ y, A *ᵥ y = 0 ↔ A.submatrix rows id *ᵥ y = 0) ∧
      Nonempty (MonicMinorData (A.submatrix rows id) d) := by
  obtain ⟨r,rows,cols,hdet,hker⟩ := exists_domain_minor A
  refine ⟨r,rows,minor_size_le rows,hker,⟨?_⟩⟩
  exact monicMinorData (A.submatrix rows id) cols hdet d (fun i j => hA (rows i) j)

end
end Decoupling.HighDim.Hermann
