import Decoupling.PolynomialPatching
import Mathlib.RingTheory.MvPolynomial.Localization
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Algebra.Polynomial.Div
import Mathlib.RingTheory.Localization.AtPrime.Basic

/-!
# Clearing constant denominators in polynomial translation witnesses

This is the local-to-global denominator step for the polynomial translation
ideal. It does not assume a Laurent local-global principle.
-/

namespace Decoupling.PolynomialPatching

open MvPolynomial IdempotentPresentation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {A B : Type*} [CommRing A] [CommRing B]

/-- Translation changes a polynomial by a multiple of the new variable. -/
theorem shift_sub_base (p : Polynomial A) :
    ∃ q : Bivariate A, shift 1 p - base p = X 1 * q := by
  have h := Polynomial.sub_dvd_eval_sub
    (X 0 + X 1 : Bivariate A) (X 0) (p.map (C : A →+* Bivariate A))
  have hd : X 1 ∣ shift (1 : A) p - base p := by
    simpa [shift, base, Polynomial.aeval_def, Polynomial.eval_map] using h
  exact hd

def coefficientMap (f : A →+* B) : Bivariate A →+* Bivariate B := MvPolynomial.map f

theorem coefficientMap_base (f : A →+* B) (p : Polynomial A) :
    coefficientMap f (base p) = base (p.map f) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n a => simp [coefficientMap, base, Polynomial.aeval_def, Polynomial.eval₂_monomial]

theorem coefficientMap_shift (f : A →+* B) (a : A) (p : Polynomial A) :
    coefficientMap f (shift a p) = shift (f a) (p.map f) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => simp [map_add, hp, hq]
  | monomial n b => simp [coefficientMap, shift, Polynomial.aeval_def, Polynomial.eval₂_monomial]

theorem coefficientMap_dilate (f : A →+* B) (a : A) (p : Bivariate A) :
    coefficientMap f (dilate a p) = dilate (f a) (coefficientMap f p) := by
  have h : (coefficientMap f).comp (dilate a).toRingHom =
      (dilate (f a)).toRingHom.comp (coefficientMap f) := by
    apply MvPolynomial.ringHom_ext
    · intro b
      simp [coefficientMap, dilate]
    · intro i
      fin_cases i <;> simp [coefficientMap, dilate]
  exact DFunLike.congr_fun h p

/-- A free idempotent has translated inverse witnesses whose constant part
in the second variable is exactly the original idempotent. -/
theorem translation_witnesses {n k : ℕ}
    (E : Matrix (Fin n) (Fin n) (Polynomial A))
    (F : Matrix (Fin n) (Fin k) (Polynomial A))
    (G : Matrix (Fin k) (Fin n) (Polynomial A))
    (hFG : F * G = E) (hGF : G * F = 1) :
    ∃ C D Q T : Matrix (Fin n) (Fin n) (Bivariate A),
      C * D = E.map (shift 1) ∧ D * C = E.map base ∧
      (∀ i j, C i j = base (E i j) + X 1 * Q i j) ∧
      (∀ i j, D i j = base (E i j) + X 1 * T i j) := by
  choose QF hQF using fun i j => shift_sub_base (F i j)
  choose QG hQG using fun i j => shift_sub_base (G i j)
  change Matrix (Fin n) (Fin k) (Bivariate A) at QF
  change Matrix (Fin k) (Fin n) (Bivariate A) at QG
  let C := F.map (shift 1) * G.map base
  let D := F.map base * G.map (shift 1)
  refine ⟨C, D, (QF : Matrix (Fin n) (Fin k) (Bivariate A)) * G.map base,
    F.map base * (QG : Matrix (Fin k) (Fin n) (Bivariate A)), ?_, ?_, ?_, ?_⟩
  · dsimp only [C, D]
    calc
      _ = F.map (shift 1) * (G.map base * F.map base) * G.map (shift 1) := by
        simp only [Matrix.mul_assoc]
      _ = E.map (shift 1) := by
        rw [← Matrix.map_mul, hGF, Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.mul_one, ← Matrix.map_mul, hFG]
  · dsimp only [C, D]
    calc
      _ = F.map base * (G.map (shift 1) * F.map (shift 1)) * G.map base := by
        simp only [Matrix.mul_assoc]
      _ = E.map base := by
        rw [← Matrix.map_mul, hGF, Matrix.map_one _ (map_zero _) (map_one _),
          Matrix.mul_one, ← Matrix.map_mul, hFG]
  · intro i j
    have hE : base (E i j) = (F.map base * G.map base) i j := by
      rw [← Matrix.map_mul, hFG]
      rfl
    rw [hE]
    simp only [C, Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [(sub_eq_iff_eq_add).mp (hQF i t)]
    ring
  · intro i j
    have hE : base (E i j) = (F.map base * G.map base) i j := by
      rw [← Matrix.map_mul, hFG]
      rfl
    rw [hE]
    simp only [D, Matrix.mul_apply, Matrix.map_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro t _
    rw [(sub_eq_iff_eq_add).mp (hQG t j)]
    ring

section Localization

variable [Algebra A B] (M : Submonoid A) [IsLocalization M B]

attribute [local instance] MvPolynomial.algebraMvPolynomial

/-- One denominator in the coefficient ring clears a finite family of
bivariate polynomials. The denominator contains no polynomial variables. -/
theorem common_constant_denominator {ι : Type*} [Finite ι] (q : ι → Bivariate B) :
    ∃ d : M, ∃ Q : ι → Bivariate A,
      ∀ i, coefficientMap (algebraMap A B) (Q i) = C (algebraMap A B d) * q i := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite
    (M.map (C : A →+* Bivariate A)) q
  obtain ⟨d₀, hd₀, he⟩ := d.property
  have hden : (d : Bivariate A) = C d₀ := he.symm
  choose Q hQ using hd
  refine ⟨⟨d₀, hd₀⟩, Q, ?_⟩
  intro i
  have hi := hQ i
  rw [Algebra.smul_def] at hi
  change coefficientMap (algebraMap A B) (Q i) =
    coefficientMap (algebraMap A B) (d : Bivariate A) * q i at hi
  simpa only [hden, coefficientMap, MvPolynomial.map_C] using hi

/-- Substituting y↦dy clears a denominator when the constant term in y
already comes from the original ring. -/
theorem dilate_clears_denominator (d : A) (p q : Bivariate B) (p₀ Q : Bivariate A)
    (hp : p = coefficientMap (algebraMap A B) p₀ + X 1 * q)
    (hQ : coefficientMap (algebraMap A B) Q = C (algebraMap A B d) * q) :
    ∃ P : Bivariate A,
      coefficientMap (algebraMap A B) P = dilate (algebraMap A B d) p := by
  refine ⟨dilate d p₀ + X 1 * dilate d Q, ?_⟩
  rw [hp, map_add, map_add, map_mul, map_mul, coefficientMap_dilate,
    coefficientMap_dilate, hQ, map_mul]
  simp [coefficientMap, dilate, mul_assoc, mul_left_comm]

/-- A basis after a coefficient localization yields an actual element of the
translation ideal outside the denominators' forbidden locus. -/
theorem denominator_mem_translationIdeal [Nontrivial B]
    (hinj : Function.Injective (algebraMap A B)) {n : ℕ}
    (E : Matrix (Fin n) (Fin n) (Polynomial A)) (hE : E * E = E)
    (hfree : Module.Free (Polynomial B) (LinearMap.range
      (E.map (Polynomial.mapRingHom (algebraMap A B))).mulVecLin)) :
    ∃ d : M, (d : A) ∈ translationIdeal E hE := by
  classical
  let EB := E.map (Polynomial.mapRingHom (algebraMap A B))
  have hEB : EB * EB = EB := by
    dsimp only [EB]
    rw [← Matrix.map_mul, hE]
  obtain ⟨k, F, G, hFG, hGF⟩ := (free_iff_factorization EB hEB).mp hfree
  obtain ⟨C, D, Q, T, hCD, hDC, hC, hD⟩ := translation_witnesses EB F G hFG hGF
  obtain ⟨d, U, hU⟩ := common_constant_denominator M
    (fun i : Fin 2 × Fin n × Fin n => if i.1 = 0 then Q i.2.1 i.2.2 else T i.2.1 i.2.2)
  have hQ (i j : Fin n) : coefficientMap (algebraMap A B) (U (0, i, j)) =
      MvPolynomial.C (algebraMap A B d) * Q i j := by simpa using hU (0, i, j)
  have hT (i j : Fin n) : coefficientMap (algebraMap A B) (U (1, i, j)) =
      MvPolynomial.C (algebraMap A B d) * T i j := by simpa using hU (1, i, j)
  have hC₀ (i j : Fin n) : C i j = coefficientMap (algebraMap A B) (base (E i j)) + X 1 * Q i j := by
    rw [coefficientMap_base]
    exact hC i j
  have hD₀ (i j : Fin n) : D i j = coefficientMap (algebraMap A B) (base (E i j)) + X 1 * T i j := by
    rw [coefficientMap_base]
    exact hD i j
  choose C' hC' using fun i j => dilate_clears_denominator (d : A)
    (C i j) (Q i j) (base (E i j)) (U (0, i, j)) (hC₀ i j) (hQ i j)
  choose D' hD' using fun i j => dilate_clears_denominator (d : A)
    (D i j) (T i j) (base (E i j)) (U (1, i, j)) (hD₀ i j) (hT i j)
  change Matrix (Fin n) (Fin n) (Bivariate A) at C' D'
  have hc : (C' : Matrix (Fin n) (Fin n) (Bivariate A)).map (coefficientMap (algebraMap A B)) =
      C.map (dilate (algebraMap A B d)) := funext fun i => funext fun j => hC' i j
  have hd : (D' : Matrix (Fin n) (Fin n) (Bivariate A)).map (coefficientMap (algebraMap A B)) =
      D.map (dilate (algebraMap A B d)) := funext fun i => funext fun j => hD' i j
  have hmap : Function.Injective
      (fun P : Matrix (Fin n) (Fin n) (Bivariate A) => P.map (coefficientMap (algebraMap A B))) := by
    intro P Q h
    funext i j
    exact MvPolynomial.map_injective (algebraMap A B) hinj (congrFun (congrFun h i) j)
  refine ⟨d, C', D', ?_, ?_⟩
  · apply hmap
    change (C' * D').map (coefficientMap (algebraMap A B)) =
      (E.map (shift (d : A))).map (coefficientMap (algebraMap A B))
    rw [Matrix.map_mul, hc, hd, ← Matrix.map_mul, hCD]
    rw [map_dilate_shift, mul_one]
    funext i j
    exact (coefficientMap_shift (algebraMap A B) d (E i j)).symm
  · apply hmap
    change (D' * C').map (coefficientMap (algebraMap A B)) =
      (E.map base).map (coefficientMap (algebraMap A B))
    rw [Matrix.map_mul, hd, hc, ← Matrix.map_mul, hDC, map_dilate_base]
    funext i j
    exact (coefficientMap_base (algebraMap A B) (E i j)).symm

end Localization

section LocalGlobal

variable [IsDomain A] {n : ℕ}
  (E : Matrix (Fin n) (Fin n) (Polynomial A)) (hE : E * E = E)

/-- The genuine polynomial local-global patching step over a domain.
All denominators are constructed; no local-to-global freeness axiom is used. -/
theorem translationIdeal_top_of_local_free
    (hlocal : ∀ (m : Ideal A) [m.IsMaximal], Module.Free (Polynomial (Localization.AtPrime m))
      (LinearMap.range (E.map
        (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime m)))).mulVecLin)) :
    translationIdeal E hE = ⊤ := by
  apply translationIdeal_top_of_maximal E hE
  intro m hm
  let := hm
  obtain ⟨d, hd⟩ := denominator_mem_translationIdeal m.primeCompl
    (IsLocalization.injective (Localization.AtPrime m) m.primeCompl_le_nonZeroDivisors)
    E hE (hlocal m)
  exact ⟨d, hd, d.property⟩

include hE in
/-- Local polynomial freeness and a free value at zero give a global basis.
The projective-module interpretation is through the actual idempotent image. -/
theorem free_of_local_free
    (hlocal : ∀ (m : Ideal A) [m.IsMaximal], Module.Free (Polynomial (Localization.AtPrime m))
      (LinearMap.range (E.map
        (Polynomial.mapRingHom (algebraMap A (Localization.AtPrime m)))).mulVecLin))
    (hzero : Module.Free A (LinearMap.range
      (E.map (Polynomial.evalRingHom (0 : A))).mulVecLin)) :
    Module.Free (Polynomial A) (LinearMap.range E.mulVecLin) :=
  free_of_translationIdeal_top E hE (translationIdeal_top_of_local_free E hE hlocal) hzero

end LocalGlobal
end
end Decoupling.PolynomialPatching
