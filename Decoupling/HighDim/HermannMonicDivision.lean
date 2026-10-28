import Decoupling.HighDim.HermannMonic
import Mathlib.Algebra.Polynomial.Div

/-!
# Total-degree bounds for actual division by a monic polynomial

HD012 Hermann induction. The hypothesis that the flattened total degree
of the monic divisor equals its degree in the distinguished variable is
precisely the weighted degree condition obtained from the linear monic
coordinate change. The proof follows actual leading-term elimination.
-/

namespace Decoupling.HighDim.Hermann

open MvPolynomial
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} [Field K] {N : ℕ}

/-- Flatten the distinguished univariate variable back to variable zero. -/
abbrev flatten : Polynomial (MvPolynomial (Fin N) K) ≃ₐ[K]
    MvPolynomial (Fin (N+1)) K := (finSuccEquiv K N).symm

private theorem finSucc_rename_succ (c : MvPolynomial (Fin N) K) :
    finSuccEquiv K N (rename Fin.succ c) = Polynomial.C c := by
  induction c using MvPolynomial.induction_on with
  | C a => simp [finSuccEquiv_apply]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp only [map_mul, rename_X, finSuccEquiv_X_succ, hp]

@[simp] theorem flatten_C (c : MvPolynomial (Fin N) K) :
    flatten (Polynomial.C c) = rename Fin.succ c := by
  apply (finSuccEquiv K N).injective
  rw [AlgEquiv.apply_symm_apply, finSucc_rename_succ]

@[simp] theorem flatten_X :
    flatten (Polynomial.X : Polynomial (MvPolynomial (Fin N) K)) = X 0 := by
  apply (finSuccEquiv K N).injective
  rw [AlgEquiv.apply_symm_apply, finSuccEquiv_X_zero]

/-- A known polynomial coefficient and a power of the distinguished variable
have the expected upper bound after actual flattening. -/
theorem flatten_C_mul_X_pow_degree_le (c : MvPolynomial (Fin N) K) (n : ℕ) :
    (flatten (Polynomial.C c * Polynomial.X ^ n)).totalDegree ≤ c.totalDegree + n := by
  rw [map_mul, map_pow, flatten_C, flatten_X]
  exact (totalDegree_mul _ _).trans
    (add_le_add (totalDegree_rename_le Fin.succ c) (totalDegree_X_pow 0 n).le)

/-- The actual leading coefficient carries the remaining part of the total
 degree. This is the crucial bound for the single division correction. -/
theorem leadingCoeff_totalDegree_add_le (P : Polynomial (MvPolynomial (Fin N) K))
    (hP : P ≠ 0) :
    P.leadingCoeff.totalDegree + P.natDegree ≤ (flatten P).totalDegree := by
  have h := totalDegree_coeff_finSuccEquiv_add_le (flatten P) P.natDegree
    (by simpa only [AlgEquiv.apply_symm_apply, Polynomial.coeff_natDegree] using Polynomial.leadingCoeff_ne_zero.mpr hP)
  simpa only [AlgEquiv.apply_symm_apply, Polynomial.coeff_natDegree] using h

/-- Simultaneous bounds on the actual `/ₘ` quotient and `%ₘ` remainder.
No positivity of the divisor degree is required; the monic constant case
and the zero dividend are covered by the same terminating elimination. -/
theorem monic_division_totalDegree (δ : Polynomial (MvPolynomial (Fin N) K))
    (hδ : δ.Monic) (hdegree : (flatten δ).totalDegree = δ.natDegree)
    (P : Polynomial (MvPolynomial (Fin N) K)) :
    (flatten (P /ₘ δ)).totalDegree ≤ (flatten P).totalDegree - δ.natDegree ∧
    (flatten (P %ₘ δ)).totalDegree ≤ (flatten P).totalDegree := by
  induction P using Polynomial.degree_lt_wf.induction with
  | h P ih =>
    by_cases hP : P = 0
    · simp [hP]
    by_cases hd : δ.degree ≤ P.degree
    · let z := Polynomial.C P.leadingCoeff * Polynomial.X ^ (P.natDegree - δ.natDegree)
      let P' := P - δ * z
      have hsmall : P'.degree < P.degree := Polynomial.div_wf_lemma ⟨hd,hP⟩ hδ
      obtain ⟨hquot,hrem⟩ := ih P' hsmall
      have hn : δ.natDegree ≤ P.natDegree := Polynomial.natDegree_le_natDegree hd
      have hlc := leadingCoeff_totalDegree_add_le P hP
      have hz : (flatten z).totalDegree ≤ (flatten P).totalDegree - δ.natDegree :=
        (flatten_C_mul_X_pow_degree_le P.leadingCoeff (P.natDegree - δ.natDegree)).trans (by omega)
      have hP' : (flatten P').totalDegree ≤ (flatten P).totalDegree := by
        change (flatten (P - δ * z)).totalDegree ≤ _
        rw [map_sub, map_mul]
        apply (totalDegree_sub _ _).trans
        apply max_le le_rfl
        apply (totalDegree_mul _ _).trans
        rw [hdegree]
        omega
      have heq : P /ₘ δ = z + P' /ₘ δ := by
        have h := Polynomial.sub_divByMonic P (δ*z) δ
        rw [Polynomial.mul_divByMonic_cancel_left z hδ] at h
        change P' /ₘ δ = P /ₘ δ - z at h
        rw [h]
        abel
      have hmod : P %ₘ δ = P' %ₘ δ := by
        change P %ₘ δ = (P - δ*z) %ₘ δ
        rw [Polynomial.sub_modByMonic, Polynomial.self_mul_modByMonic hδ, sub_zero]
      constructor
      · rw [heq, map_add]
        exact (totalDegree_add _ _).trans (max_le hz (hquot.trans (Nat.sub_le_sub_right hP' _)))
      · rw [hmod]
        exact hrem.trans hP'
    · have hlt : P.degree < δ.degree := lt_of_not_ge hd
      rw [(Polynomial.divByMonic_eq_zero_iff hδ).mpr hlt,
        (Polynomial.modByMonic_eq_self_iff hδ).mpr hlt]
      simp

/-- Actual monic remainder does not increase flattened total degree. -/
theorem modByMonic_totalDegree_le (δ : Polynomial (MvPolynomial (Fin N) K))
    (hδ : δ.Monic) (hdegree : (flatten δ).totalDegree = δ.natDegree)
    (P : Polynomial (MvPolynomial (Fin N) K)) :
    (flatten (P %ₘ δ)).totalDegree ≤ (flatten P).totalDegree :=
  (monic_division_totalDegree δ hδ hdegree P).2

/-- Actual monic quotient lowers flattened total degree by the divisor degree. -/
theorem divByMonic_totalDegree_le (δ : Polynomial (MvPolynomial (Fin N) K))
    (hδ : δ.Monic) (hdegree : (flatten δ).totalDegree = δ.natDegree)
    (P : Polynomial (MvPolynomial (Fin N) K)) :
    (flatten (P /ₘ δ)).totalDegree ≤ (flatten P).totalDegree - δ.natDegree :=
  (monic_division_totalDegree δ hδ hdegree P).1

end
end Decoupling.HighDim.Hermann
