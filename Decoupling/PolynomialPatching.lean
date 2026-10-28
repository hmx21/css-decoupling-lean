import Decoupling.IdempotentPresentation
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.Ring
import Mathlib.RingTheory.Ideal.Maximal

/-!
# Polynomial translation ideal for projective patching

This is strictly polynomial patching, using the translation-ideal argument
of Dicks, arXiv:2112.02272v1, Theorem 5. There is no claim of a Laurent
local-global principle (the analogous general statement is false).
-/

namespace Decoupling.PolynomialPatching

open IdempotentPresentation

noncomputable section

variable {A : Type*} [CommRing A]

abbrev Bivariate (A : Type*) [CommRing A] := MvPolynomial (Fin 2) A

def base : Polynomial A →ₐ[A] Bivariate A := Polynomial.aeval (MvPolynomial.X 0)

def shift (a : A) : Polynomial A →ₐ[A] Bivariate A :=
  Polynomial.aeval (MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 1)

def translate (a : A) : Bivariate A →ₐ[A] Bivariate A :=
  MvPolynomial.aeval ![MvPolynomial.X 0 + MvPolynomial.C a * MvPolynomial.X 1,
    MvPolynomial.X 1]

def dilate (a : A) : Bivariate A →ₐ[A] Bivariate A :=
  MvPolynomial.aeval ![MvPolynomial.X 0, MvPolynomial.C a * MvPolynomial.X 1]

theorem shift_zero : shift (0 : A) = base := by
  apply Polynomial.algHom_ext
  simp [shift, base]

theorem translate_base (a : A) : (translate a).comp base = shift a := by
  apply Polynomial.algHom_ext
  simp [translate, base, shift]

theorem translate_shift (a b : A) : (translate b).comp (shift a) = shift (a + b) := by
  apply Polynomial.algHom_ext
  simp [translate, shift]
  ring

theorem dilate_base (a : A) : (dilate a).comp base = base := by
  apply Polynomial.algHom_ext
  simp [dilate, base]

theorem dilate_shift (a b : A) : (dilate b).comp (shift a) = shift (b * a) := by
  apply Polynomial.algHom_ext
  simp [dilate, shift]
  ring

variable {n : ℕ} (E : Matrix (Fin n) (Fin n) (Polynomial A)) (hE : E * E = E)

include hE in
theorem mapped_idempotent (f : Polynomial A →ₐ[A] Bivariate A) :
    E.map f * E.map f = E.map f := by
  rw [← Matrix.map_mul, hE]

theorem map_translate_base (a : A) : (E.map base).map (translate a) = E.map (shift a) := by
  funext i j
  exact DFunLike.congr_fun (translate_base a) (E i j)

theorem map_translate_shift (a b : A) :
    (E.map (shift a)).map (translate b) = E.map (shift (a + b)) := by
  funext i j
  exact DFunLike.congr_fun (translate_shift a b) (E i j)

theorem map_dilate_base (a : A) : (E.map base).map (dilate a) = E.map base := by
  funext i j
  exact DFunLike.congr_fun (dilate_base a) (E i j)

theorem map_dilate_shift (a b : A) :
    (E.map (shift a)).map (dilate b) = E.map (shift (b * a)) := by
  funext i j
  exact DFunLike.congr_fun (dilate_shift a b) (E i j)

/-- Scalars for which the translated idempotent has the same projective image.
The ideal laws are proved by actual polynomial substitutions on witnesses. -/
def translationIdeal : Ideal A where
  carrier := {a | Related (E.map (shift a)) (E.map base)}
  zero_mem' := by
    change Related (E.map (shift (0 : A))) (E.map base)
    rw [shift_zero]
    exact Related.refl (mapped_idempotent E hE base)
  add_mem' := by
    intro a b ha hb
    have ht := ha.map (translate b).toRingHom
    change Related ((E.map (shift a)).map (translate b)) ((E.map base).map (translate b)) at ht
    rw [map_translate_shift, map_translate_base] at ht
    exact ht.trans hb (mapped_idempotent E hE (shift (a + b))) (mapped_idempotent E hE base)
  smul_mem' := by
    intro a b hb
    have ht := hb.map (dilate a).toRingHom
    change Related ((E.map (shift b)).map (dilate a)) ((E.map base).map (dilate a)) at ht
    rw [map_dilate_shift, map_dilate_base] at ht
    exact ht

/-- Substitute y = -x, keeping the polynomial coefficient ring fixed. -/
def cancelShift : Bivariate A →ₐ[A] Polynomial A :=
  MvPolynomial.aeval ![Polynomial.X, -Polynomial.X]

theorem cancelShift_base : (cancelShift (A := A)).comp base = AlgHom.id A (Polynomial A) := by
  apply Polynomial.algHom_ext
  simp [cancelShift, base]

theorem cancelShift_shift_one :
    (cancelShift (A := A)).comp (shift 1) = Polynomial.aeval (0 : Polynomial A) := by
  apply Polynomial.algHom_ext
  simp [cancelShift, shift]

/-- The translation ideal being the unit ideal produces actual rectangular
matrix factors relating E to its value at x=0. -/
theorem related_constant_of_translationIdeal_top (h : translationIdeal E hE = ⊤) :
    Related E (E.map (Polynomial.aeval (0 : Polynomial A))) := by
  have h1 : Related (E.map (shift 1)) (E.map base) := by
    change (1 : A) ∈ translationIdeal E hE
    rw [h]
    trivial
  have ht := h1.map (cancelShift (A := A)).toRingHom
  have hb : (E.map base).map (cancelShift (A := A)) = E := by
    funext i j
    exact DFunLike.congr_fun cancelShift_base (E i j)
  have hs : (E.map (shift 1)).map (cancelShift (A := A)) =
      E.map (Polynomial.aeval (0 : Polynomial A)) := by
    funext i j
    exact DFunLike.congr_fun cancelShift_shift_one (E i j)
  change Related ((E.map (shift 1)).map cancelShift) ((E.map base).map cancelShift) at ht
  rw [hb, hs] at ht
  exact ht.symm

theorem translationIdeal_top_of_maximal
    (h : ∀ m : Ideal A, m.IsMaximal →
      ∃ a : A, a ∈ translationIdeal E hE ∧ a ∉ m) : translationIdeal E hE = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (translationIdeal E hE) hne
  obtain ⟨a, ha, hna⟩ := h m hm
  exact hna (hle ha)

/-- Patching together with a free special fiber gives native polynomial
module freeness through explicit rectangular inverse factors. -/
theorem free_of_translationIdeal_top [Nontrivial A]
    (h : translationIdeal E hE = ⊤)
    (hfree : Module.Free A (LinearMap.range
      (E.map (Polynomial.evalRingHom (0 : A))).mulVecLin)) :
    Module.Free (Polynomial A) (LinearMap.range E.mulVecLin) := by
  let E₀ := E.map (Polynomial.evalRingHom (0 : A))
  have h₀ : E₀ * E₀ = E₀ := by
    dsimp only [E₀]
    rw [← Matrix.map_mul, hE]
  obtain ⟨k, F, G, hFG, hGF⟩ := (free_iff_factorization E₀ h₀).mp hfree
  have hrel : Related E₀ (1 : Matrix (Fin k) (Fin k) A) := ⟨F, G, hFG, hGF⟩
  have hm := hrel.map (Polynomial.C : A →+* Polynomial A)
  have he : E₀.map Polynomial.C = E.map (Polynomial.aeval (0 : Polynomial A)) := by
    funext i j
    simp [E₀, Polynomial.aeval_def, Polynomial.eval₂_at_zero,
      Polynomial.coeff_zero_eq_eval_zero]
  rw [he, Matrix.map_one _ (map_zero _) (map_one _)] at hm
  have ht := (related_constant_of_translationIdeal_top E hE h).trans hm hE
    (Matrix.one_mul _)
  obtain ⟨F', G', hFG', hGF'⟩ := ht
  exact free_of_factorization E hE F' G' hFG' hGF'

end
end Decoupling.PolynomialPatching
