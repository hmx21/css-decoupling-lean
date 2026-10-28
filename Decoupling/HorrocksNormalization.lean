import Decoupling.HorrocksProjection
import Decoupling.IdempotentPresentation
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Residue normalization of idempotent factors

The residue polynomial ring is a PID. Its actual free idempotent image
provides polynomial factors; lifting their comparison matrix normalizes
the given monic-localization factors without changing their products.
-/

namespace Decoupling.HorrocksNormalization

open MonicLocalization MonicResidue HorrocksProjection Polynomial Matrix

noncomputable section

set_option maxHeartbeats 800000

private theorem comparison {S : Type*} [CommRing S] {n m k : ℕ}
    (E : Matrix (Fin n) (Fin n) S)
    (F : Matrix (Fin n) (Fin m) S) (G : Matrix (Fin m) (Fin n) S)
    (C : Matrix (Fin n) (Fin k) S) (D : Matrix (Fin k) (Fin n) S)
    (hFG : F * G = E) (hGF : G * F = 1) (hCD : C * D = E) (hDC : D * C = 1) :
    (D * F) * (G * C) = 1 ∧ (G * C) * (D * F) = 1 ∧
      F * (G * C) = C ∧ (D * F) * G = D := by
  have hEC : E * C = C := by rw [← hCD, Matrix.mul_assoc, hDC, Matrix.mul_one]
  have hDE : D * E = D := by rw [← hCD, ← Matrix.mul_assoc, hDC, Matrix.one_mul]
  have hEF : E * F = F := by rw [← hFG, Matrix.mul_assoc, hGF, Matrix.mul_one]
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc
      (D * F) * (G * C) = D * (F * G) * C := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hFG, hDE, hDC]
  · calc
      (G * C) * (D * F) = G * ((C * D) * F) := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hCD, hEF, hGF]
  · rw [← Matrix.mul_assoc, hFG, hEC]
  · rw [Matrix.mul_assoc, hFG, hDE]

private theorem size_eq_of_inverse {S : Type*} [Field S] {m k : ℕ}
    (U : Matrix (Fin k) (Fin m) S) (V : Matrix (Fin m) (Fin k) S)
    (hUV : U * V = 1) (hVU : V * U = 1) : m = k := by
  let e : (Fin m → S) ≃ₗ[S] (Fin k → S) :=
    { toLinearMap := U.mulVecLin
      invFun := V.mulVec
      left_inv := fun v => by
        change V *ᵥ (U *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, hVU, Matrix.one_mulVec]
      right_inv := fun v => by
        change U *ᵥ (V *ᵥ v) = v
        rw [Matrix.mulVec_mulVec, hUV, Matrix.one_mulVec] }
  simpa only [Module.finrank_pi, Fintype.card_fin] using e.finrank_eq

variable {A : Type*} [CommRing A] [IsLocalRing A] {n m : ℕ}

/-- Any monic-localization factorization of a polynomial idempotent can
be changed by an actual invertible matrix so that both factors have
polynomial residues. -/
theorem normalized_factors
    (E : Matrix (Fin n) (Fin n) A[X]) (hE : E * E = E)
    (F : Matrix (Fin n) (Fin m) (MonicFrac A))
    (G : Matrix (Fin m) (Fin n) (MonicFrac A))
    (hFG : F * G = E.map (algebraMap A[X] (MonicFrac A))) (hGF : G * F = 1) :
    ∃ F' : Matrix (Fin n) (Fin m) (MonicFrac A),
    ∃ G' : Matrix (Fin m) (Fin n) (MonicFrac A),
      F' * G' = E.map (algebraMap A[X] (MonicFrac A)) ∧ G' * F' = 1 ∧
      (∀ i j, F' i j ∈ residuePolynomialSubring (A := A)) ∧
      (∀ i j, G' i j ∈ residuePolynomialSubring (A := A)) := by
  classical
  let K := IsLocalRing.ResidueField A
  let π := Polynomial.mapRingHom (IsLocalRing.residue A)
  let ι := algebraMap K[X] (MonicFrac K)
  let ρ := residueMap A
  let E₀ := E.map π
  let F₀ := F.map ρ
  let G₀ := G.map ρ
  have hE₀ : E₀ * E₀ = E₀ := by
    change π.mapMatrix E * π.mapMatrix E = π.mapMatrix E
    rw [← map_mul, hE]
  obtain ⟨k, ⟨b⟩⟩ := (LinearMap.range E₀.mulVecLin).nonempty_basis_of_pid
    (Pi.basisFun K[X] (Fin n))
  obtain ⟨C, D, hCD, hDC⟩ :=
    IdempotentPresentation.factors_of_equiv E₀ hE₀ b.equivFun.symm
  have hFG₀ : F₀ * G₀ = E₀.map ι := by
    change F.map ρ * G.map ρ = _
    rw [← Matrix.map_mul, hFG]
    funext i j
    exact mapCoefficients_polynomialInclusion (IsLocalRing.residue A) (E i j)
  have hGF₀ : G₀ * F₀ = 1 := by
    change G.map ρ * F.map ρ = 1
    rw [← Matrix.map_mul, hGF]
    exact map_one ρ.mapMatrix
  have hCD₀ : C.map ι * D.map ι = E₀.map ι := by
    rw [← Matrix.map_mul, hCD]
  have hDC₀ : D.map ι * C.map ι = 1 := by
    rw [← Matrix.map_mul, hDC]
    exact map_one ι.mapMatrix
  obtain ⟨hUV, hVU, hFC, hDG⟩ :=
    comparison (E₀.map ι) F₀ G₀ (C.map ι) (D.map ι) hFG₀ hGF₀ hCD₀ hDC₀
  have hmk : m = k := size_eq_of_inverse _ _ hUV hVU
  subst k
  let U₀ := D.map ι * F₀
  let V₀ := G₀ * C.map ι
  obtain ⟨U, hU, hmapU⟩ := residue_GL_lifts A U₀ (IsUnit.of_mul_eq_one V₀ hUV)
  let u := hU.unit
  have hu : (u : Matrix (Fin m) (Fin m) (MonicFrac A)) = U := hU.unit_spec
  have hmapu : ((u : Matrix (Fin m) (Fin m) (MonicFrac A))).map ρ = U₀ := hu ▸ hmapU
  have hmapinv : (u.inv : Matrix (Fin m) (Fin m) (MonicFrac A)).map ρ = V₀ := by
    have hm : (u.inv : Matrix (Fin m) (Fin m) (MonicFrac A)).map ρ * U₀ = 1 := by
      rw [← hmapu, ← Matrix.map_mul, u.inv_val]
      exact map_one ρ.mapMatrix
    calc
      (u.inv : Matrix (Fin m) (Fin m) (MonicFrac A)).map ρ =
          (u.inv : Matrix (Fin m) (Fin m) (MonicFrac A)).map ρ * (U₀ * V₀) := by rw [hUV, Matrix.mul_one]
      _ = V₀ := by rw [← Matrix.mul_assoc, hm, Matrix.one_mul]
  refine ⟨F * u.inv, u.val * G, ?_, ?_, ?_, ?_⟩
  · calc
      (F * u.inv) * (u.val * G) = F * (u.inv * u.val) * G := by simp only [Matrix.mul_assoc]
      _ = E.map (algebraMap A[X] (MonicFrac A)) := by rw [u.inv_val, Matrix.mul_one, hFG]
  · calc
      (u.val * G) * (F * u.inv) = u.val * (G * F) * u.inv := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hGF, Matrix.mul_one, u.val_inv]
  · intro i j
    refine ⟨C i j, ?_⟩
    have hm : (F * u.inv).map ρ = C.map ι := by
      rw [Matrix.map_mul]
      change F₀ * (u.inv : Matrix (Fin m) (Fin m) (MonicFrac A)).map ρ = _
      rw [hmapinv]
      exact hFC
    exact (congrFun (congrFun hm i) j).symm
  · intro i j
    refine ⟨D i j, ?_⟩
    have hm : (u.val * G).map ρ = D.map ι := by
      rw [Matrix.map_mul]
      change (u.val : Matrix (Fin m) (Fin m) (MonicFrac A)).map ρ * G₀ = _
      rw [hmapu]
      exact hDG
    exact (congrFun (congrFun hm i) j).symm

end

end Decoupling.HorrocksNormalization
