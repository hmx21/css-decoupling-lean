import Decoupling.HorrocksNormalization

/-!
# Local Horrocks theorem for actual idempotent images

For a commutative local ring `A`, a polynomial idempotent whose image is
free after inverting all monic polynomials already has a free image over
`A[X]`. The proof constructs rectangular polynomial inverse factors.
It follows Dicks, arXiv:2112.02272v1, Theorem 4, in column-vector notation.
-/

namespace Decoupling.LocalHorrocks

open MonicLocalization MonicResidue HorrocksProjection HorrocksNormalization
  Polynomial Matrix

noncomputable section

set_option maxHeartbeats 800000

variable {A : Type*} [CommRing A] [IsLocalRing A] {n m : ℕ}

private theorem product_mem {a b c : ℕ}
    (F : Matrix (Fin a) (Fin b) (MonicFrac A))
    (G : Matrix (Fin b) (Fin c) (MonicFrac A))
    (hF : ∀ i j, F i j ∈ residuePolynomialSubring (A := A))
    (hG : ∀ i j, G i j ∈ residuePolynomialSubring (A := A)) :
    ∀ i j, (F * G) i j ∈ residuePolynomialSubring (A := A) := by
  intro i j
  change (∑ k, F i k * G k j) ∈ residuePolynomialSubring (A := A)
  apply (residuePolynomialSubring (A := A)).sum_mem
  intro k _
  exact (residuePolynomialSubring (A := A)).mul_mem (hF i k) (hG k j)

private theorem map_polynomialPart_inclusion {a b : ℕ}
    (P : Matrix (Fin a) (Fin b) A[X]) :
    (P.map (algebraMap A[X] (MonicFrac A))).map polynomialPart = P := by
  funext i j
  exact polynomialPart_algebraMap (P i j)

/-- Monic-localized inverse factors descend to actual polynomial inverse
factors. No freeness or generation conclusion is included in the hypotheses. -/
theorem polynomial_factors
    (E : Matrix (Fin n) (Fin n) A[X]) (hE : E * E = E)
    (F : Matrix (Fin n) (Fin m) (MonicFrac A))
    (G : Matrix (Fin m) (Fin n) (MonicFrac A))
    (hFG : F * G = E.map (algebraMap A[X] (MonicFrac A))) (hGF : G * F = 1) :
    ∃ P : Matrix (Fin n) (Fin m) A[X], ∃ Q : Matrix (Fin m) (Fin n) A[X],
      P * Q = E ∧ Q * P = 1 := by
  classical
  obtain ⟨F, G, hFG, hGF, hF, hG⟩ := normalized_factors E hE F G hFG hGF
  let f := algebraMap A[X] (MonicFrac A)
  let ρ := residueMap A
  have ht : F.transpose * G.transpose = 1 := by
    rw [← Matrix.transpose_mul, hGF, Matrix.transpose_one]
  obtain ⟨H, hH⟩ := exists_right_projection F.transpose G.transpose ht (fun i j => hG j i)
  let L := H.transpose
  let U := L.map f * F
  have hU : U.map polynomialPart = 1 := by
    have h := congrArg Matrix.transpose hH
    change (F.transpose * (H.map f)).transpose.map polynomialPart = _ at h
    rw [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h
    exact h
  have hUr : ∀ i j, U i j ∈ residuePolynomialSubring (A := A) :=
    product_mem (L.map f) F (fun i j => polynomialInclusion_mem (L i j)) hF
  have hρU : U.map ρ = 1 := by
    funext i j
    have h := residue_polynomialPart (hUr i j)
    have hp : polynomialPart (U i j) = (1 : Matrix (Fin m) (Fin m) A[X]) i j :=
      congrFun (congrFun hU i) j
    rw [hp] at h
    change residueMap A (U i j) = (1 : Matrix (Fin m) (Fin m)
      (MonicFrac (IsLocalRing.ResidueField A))) i j
    rw [← h]
    simp only [Matrix.one_apply, polynomialInclusion_apply, apply_ite,
      map_one, map_zero]
    split_ifs <;> rfl
  let u := (Horrocks.isUnit_of_polynomialPart_eq_one U hU).unit
  have hu : u.val = U := (Horrocks.isUnit_of_polynomialPart_eq_one U hU).unit_spec
  have hρinv : u.inv.map ρ = 1 := by
    have h := congrArg (fun V : Matrix (Fin m) (Fin m) (MonicFrac A) => V.map ρ) u.inv_val
    rw [Matrix.map_mul, hu, hρU, Matrix.mul_one] at h
    exact h.trans (Matrix.map_one ρ (map_zero ρ) (map_one ρ))
  have hir : ∀ i j, u.inv i j ∈ residuePolynomialSubring (A := A) := by
    intro i j
    refine ⟨(1 : Matrix (Fin m) (Fin m) (IsLocalRing.ResidueField A)[X]) i j, ?_⟩
    have h := congrFun (congrFun hρinv i) j
    change residueMap A (u.inv i j) = (1 : Matrix (Fin m) (Fin m)
      (MonicFrac (IsLocalRing.ResidueField A))) i j at h
    rw [h]
    simp only [Matrix.one_apply, apply_ite, map_one, map_zero]
    split_ifs <;> rfl
  let F' := F * u.inv
  let G' := u.val * G
  have hF' : ∀ i j, F' i j ∈ residuePolynomialSubring (A := A) := product_mem F u.inv hF hir
  have hFG' : F' * G' = E.map f := by
    change (F * u.inv) * (u.val * G) = _
    calc
      (F * u.inv) * (u.val * G) = F * (u.inv * u.val) * G := by simp only [Matrix.mul_assoc]
      _ = E.map f := by rw [u.inv_val, Matrix.mul_one, hFG]
  have hGF' : G' * F' = 1 := by
    change (u.val * G) * (F * u.inv) = _
    calc
      (u.val * G) * (F * u.inv) = u.val * (G * F) * u.inv := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hGF, Matrix.mul_one, u.val_inv]
  let Q := L * E
  have hQ : Q.map f = G' := by
    change (L * E).map f = u.val * G
    rw [Matrix.map_mul, hu]
    change L.map f * E.map f = (L.map f * F) * G
    rw [Matrix.mul_assoc, hFG]
  obtain ⟨H', hH'⟩ := exists_right_projection G' F' hGF' hF'
  have hQH : Q * H' = 1 := by
    rw [← hQ, ← Matrix.map_mul, map_polynomialPart_inclusion] at hH'
    exact hH'
  have hHloc : G' * H'.map f = 1 := by
    rw [← hQ, ← Matrix.map_mul, hQH]
    exact Matrix.map_one f (map_zero f) (map_one f)
  let P := E * H'
  have hP : P.map f = F' := by
    change (E * H').map f = F'
    rw [Matrix.map_mul, ← hFG', Matrix.mul_assoc, hHloc, Matrix.mul_one]
  have hinj {a b : ℕ} : Function.Injective
      (fun V : Matrix (Fin a) (Fin b) A[X] => V.map f) := by
    intro V W h
    funext i j
    exact polynomialInclusion_injective (congrFun (congrFun h i) j)
  refine ⟨P, Q, hinj ?_, hinj ?_⟩
  · change (P * Q).map f = E.map f
    rw [Matrix.map_mul, hP, hQ, hFG']
  · change (Q * P).map f = (1 : Matrix (Fin m) (Fin m) A[X]).map f
    rw [Matrix.map_mul, hQ, hP, hGF']
    exact (Matrix.map_one f (map_zero f) (map_one f)).symm

/-- The local Horrocks theorem, expressed using the actual native image
of a polynomial idempotent matrix and native `Module.Free`. -/
theorem free_range_of_monic_free
    (E : Matrix (Fin n) (Fin n) A[X]) (hE : E * E = E)
    (hf : Module.Free (MonicFrac A)
      (LinearMap.range (E.map (algebraMap A[X] (MonicFrac A))).mulVecLin)) :
    Module.Free A[X] (LinearMap.range E.mulVecLin) := by
  let : Nontrivial (MonicFrac A) :=
    Function.Injective.nontrivial polynomialInclusion_injective
  have he : E.map (algebraMap A[X] (MonicFrac A)) *
      E.map (algebraMap A[X] (MonicFrac A)) = E.map (algebraMap A[X] (MonicFrac A)) := by
    rw [← Matrix.map_mul, hE]
  obtain ⟨m, F, G, hFG, hGF⟩ :=
    (IdempotentPresentation.free_iff_factorization _ he).mp hf
  obtain ⟨P, Q, hPQ, hQP⟩ := polynomial_factors E hE F G hFG hGF
  exact (IdempotentPresentation.free_iff_factorization E hE).mpr ⟨m, P, Q, hPQ, hQP⟩

end

end Decoupling.LocalHorrocks
