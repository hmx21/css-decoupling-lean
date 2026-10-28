import Decoupling.HighDim.HermannInhomogeneousReduction
import Decoupling.HighDim.HermannCoefficientDegree
import Decoupling.HighDim.HermannMonicDivision
import Decoupling.HighDim.HermannSolutionReindex

/-!
# The quantitative inhomogeneous induction step after actual normalization

Every normalized input below is supplied by the constructed maximal-minor
normalization in the final theorem. This step proves bounded solvability by
coefficient reduction, the smaller-variable induction hypothesis, and the
explicit adjugate lift; it does not assume bounded solvability of this system.
-/

namespace Decoupling.HighDim.Hermann
open Polynomial Matrix MvPolynomial
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {N r n d : ℕ}

/-- Degree in the distinguished variable is bounded by genuine total degree. -/
theorem natDegree_le_totalDegree_flatten (P : Polynomial (MvPolynomial (Fin N) K)) :
    P.natDegree ≤ (flatten P).totalDegree := by
  have h := MvPolynomial.degreeOf_le_totalDegree (flatten P) 0
  rw [← MvPolynomial.natDegree_finSuccEquiv] at h
  simpa only [flatten, AlgEquiv.apply_symm_apply] using h

theorem coefficient_totalDegree_le_flatten (P : Polynomial (MvPolynomial (Fin N) K))
    (d : ℕ) (h : (flatten P).totalDegree ≤ d) (k : ℕ) : (P.coeff k).totalDegree ≤ d := by
  have he := finSucc_coefficient_totalDegree_le (flatten P) d h k
  simpa only [flatten, AlgEquiv.apply_symm_apply] using he

/-- The actual encoding of a finite coefficient solution solves the polynomial equation. -/
theorem lastEncode_solves
    {S : Type*} [CommRing S] {m n d b : ℕ}
    (A : Matrix (Fin m) (Fin n) S[X]) (hA : ∀ i j, (A i j).natDegree ≤ d)
    (v : Fin m → S[X]) (hv : ∀ i, (v i).degree < ((d + b : ℕ) : WithBot ℕ))
    (z : (Fin n × Fin b) → S)
    (hz : lastCoefficientMatrix A d b *ᵥ z = lastDecode (d + b) v) :
    A *ᵥ lastEncode b z = v := by
  rw [lastCoefficientMatrix_mulVec] at hz
  have he := congrArg (lastEncode (d + b)) hz
  rw [lastEncode_decode _ _ (mulVec_degree_lt A d b hA _ (lastEncode_degree b z)),
    lastEncode_decode _ _ hv] at he
  exact he

/-- The complete smaller-variable solve and reconstruction step, with all
added degrees included in the conservative recurrence. -/
theorem bounded_solution_normalized
    (IH : ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
      (v : Fin m → MvPolynomial (Fin N) K),
      (∀ i j, (A i j).totalDegree ≤ d) → (∀ i, (v i).totalDegree ≤ d) →
      (∃ y, A *ᵥ y = v) → ∃ y, A *ᵥ y = v ∧ ∀ j,
        (y j).totalDegree ≤ solutionBound N m d)
    (hr : 1 ≤ r) (hd : 1 ≤ d)
    (A : Matrix (Fin r) (Fin n) (Polynomial (MvPolynomial (Fin N) K)))
    (H : Matrix (Fin n) (Fin r) (Polynomial (MvPolynomial (Fin N) K)))
    (E : Matrix (Fin n) (Fin n) (Polynomial (MvPolynomial (Fin N) K)))
    (δ : Polynomial (MvPolynomial (Fin N) K)) (hδ : δ.Monic)
    (hδdegree : (flatten δ).totalDegree = δ.natDegree)
    (hAH : A * H = δ • 1) (hEeq : E = δ • 1 - H * A)
    (hA : ∀ i j, (flatten (A i j)).totalDegree ≤ d)
    (hH : ∀ i j, (flatten (H i j)).totalDegree ≤ r * d)
    (hE : ∀ i j, (flatten (E i j)).totalDegree ≤ r * d)
    (v : Fin r → Polynomial (MvPolynomial (Fin N) K))
    (hv : ∀ i, (flatten (v i)).totalDegree ≤ d) (hsol : ∃ y, A *ᵥ y = v) :
    ∃ y, A *ᵥ y = v ∧ ∀ j, (flatten (y j)).totalDegree ≤ solutionBound (N + 1) r d := by
  classical
  let M := r * d
  have hM : 0 < M := Nat.mul_pos (by omega) (by omega)
  have hAnat : ∀ i j, (A i j).natDegree ≤ d := fun i j =>
    (natDegree_le_totalDegree_flatten _).trans (hA i j)
  let g := rhsRemainder δ v
  have hg : ∀ i, (flatten (g i)).totalDegree ≤ d := fun i =>
    (modByMonic_totalDegree_le δ hδ hδdegree (v i)).trans (hv i)
  have hglast : ∀ i, (g i).degree < ((d + M : ℕ) : WithBot ℕ) := by
    intro i
    apply Polynomial.degree_le_natDegree.trans_lt
    apply (WithBot.coe_le_coe.mpr ((natDegree_le_totalDegree_flatten _).trans (hg i))).trans_lt
    exact WithBot.coe_lt_coe.mpr (show d < d + M by omega)
  have hsmall : ∃ z, A *ᵥ z = g ∧ ∀ j, (z j).degree < (M : WithBot ℕ) :=
    exists_reduced_inhomogeneous_solution δ hδ A H E hAH hEeq M
      (fun i j => (natDegree_le_totalDegree_flatten _).trans (hE i j))
      (fun i j => (natDegree_le_totalDegree_flatten _).trans (hH i j)) v hsol
  let B := lastCoefficientMatrix A d M
  let w := lastDecode (d + M) g
  have hB : ∀ i j, (B i j).totalDegree ≤ d := by
    intro i j
    dsimp only [B, lastCoefficientMatrix]
    split
    · exact coefficient_totalDegree_le_flatten (A i.1 j.1) d (hA i.1 j.1) _
    · simp
  have hw : ∀ i, (w i).totalDegree ≤ d := fun i =>
    coefficient_totalDegree_le_flatten (g i.1) d (hg i.1) i.2.val
  have hBs : ∃ z, B *ᵥ z = w := (last_bounded_solution_iff A d M hAnat g hglast).mp hsmall
  obtain ⟨z, hz, hdegz⟩ := bounded_solution_finite_labels IH B w hB hw hBs
  have hzpoly : A *ᵥ lastEncode M z = g := lastEncode_solves A hAnat g hglast z hz
  refine ⟨lastEncode M z + inhomogeneousLift δ H v,
    equation_add_lift δ A H hAH v _ hzpoly, ?_⟩
  intro j
  have hrows : Fintype.card (Fin r × Fin (d + M)) = nextRows r d := by
    simp only [Fintype.card_prod, Fintype.card_fin, M, nextRows]
    ring
  have hrec : ∀ i, (z i).totalDegree ≤ solutionBound N (nextRows r d) d := by
    simpa only [hrows] using hdegz
  have hlow := lastEncode_totalDegree_le M (solutionBound N (nextRows r d) d) z hrec j
  have hlift : (flatten (inhomogeneousLift δ H v j)).totalDegree ≤ M + d := by
    change (flatten (∑ i, H j i * (v i /ₘ δ))).totalDegree ≤ _
    rw [map_sum]
    apply MvPolynomial.totalDegree_finsetSum_le
    intro i _
    rw [map_mul]
    exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hH j i)
      ((divByMonic_totalDegree_le δ hδ hδdegree (v i)).trans
        ((Nat.sub_le _ _).trans (hv i))))
  change (flatten (lastEncode M z j + inhomogeneousLift δ H v j)).totalDegree ≤ _
  rw [map_add]
  apply (MvPolynomial.totalDegree_add _ _).trans
  apply max_le
  · apply hlow.trans
    dsimp only [solutionBound]
    dsimp [M]
    nlinarith [Nat.sub_le (r * d) 1]
  · apply hlift.trans
    have hdm : d ≤ r * d := by simpa using Nat.mul_le_mul_right d hr
    dsimp only [solutionBound]
    dsimp [M]
    nlinarith

end
end Decoupling.HighDim.Hermann
