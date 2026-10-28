import Decoupling.MonicLocalization
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Polynomial.DegreeLT
import Mathlib.RingTheory.Nakayama
import Mathlib.RingTheory.LocalRing.Module

/-!
# Algebraic normalization for the Horrocks argument

These lemmas establish the proper-fraction determinant step in Dicks,
arXiv:2112.02272v1, Theorem 4. They do not assert the complete local
freeness theorem: the residue-field lifting and Nakayama surjectivity
steps are separate obligations.
-/

namespace Decoupling.Horrocks

open MonicLocalization Matrix Polynomial

noncomputable section

variable {A : Type*} [CommRing A] [Nontrivial A]

omit [Nontrivial A] in
private theorem product_zero_or_one {ι : Type*} (s : Finset ι)
    (b : ι → MonicFrac A) (hb : ∀ i ∈ s, b i = 0 ∨ b i = 1) :
    ∏ i ∈ s, b i = 0 ∨ ∏ i ∈ s, b i = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi]
    rcases hb i (Finset.mem_insert_self _ _) with h | h
    · simp [h]
    · simpa [h] using ih (fun j hj => hb j (Finset.mem_insert_of_mem hj))

private theorem perturbation_mul_mem {a b c d : MonicFrac A}
    (hb : b = 0 ∨ b = 1) (hd : d = 0 ∨ d = 1)
    (hab : a - b ∈ properFractions (A := A))
    (hcd : c - d ∈ properFractions (A := A)) :
    a * c - b * d ∈ properFractions (A := A) := by
  have h₁ := properFractions_mul hab hcd
  have h₂ : (a - b) * d ∈ properFractions (A := A) := by
    rcases hd with rfl | rfl
    · simp
    · simpa using hab
  have h₃ : b * (c - d) ∈ properFractions (A := A) := by
    rcases hb with rfl | rfl
    · simp
    · simpa using hcd
  convert (properFractions (A := A)).add_mem
    ((properFractions (A := A)).add_mem h₁ h₂) h₃ using 1
  ring

private theorem product_perturbation_mem {ι : Type*} (s : Finset ι)
    (a b : ι → MonicFrac A) (hb : ∀ i ∈ s, b i = 0 ∨ b i = 1)
    (hab : ∀ i ∈ s, a i - b i ∈ properFractions (A := A)) :
    (∏ i ∈ s, a i) - ∏ i ∈ s, b i ∈ properFractions (A := A) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact perturbation_mul_mem (hb i (Finset.mem_insert_self _ _))
      (product_zero_or_one s b (fun j hj => hb j (Finset.mem_insert_of_mem hj)))
      (hab i (Finset.mem_insert_self _ _))
      (ih (fun j hj => hb j (Finset.mem_insert_of_mem hj))
        (fun j hj => hab j (Finset.mem_insert_of_mem hj)))

/-- If every matrix entry differs from the identity by a proper fraction,
its determinant differs from one by a proper fraction. -/
theorem det_sub_one_mem {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι (MonicFrac A))
    (hU : ∀ i j, U i j - (1 : Matrix ι ι (MonicFrac A)) i j ∈ properFractions (A := A)) :
    U.det - 1 ∈ properFractions (A := A) := by
  classical
  rw [← det_one (n := ι) (R := MonicFrac A), det_apply, det_apply, ← Finset.sum_sub_distrib]
  apply (properFractions (A := A)).sum_mem
  intro σ _
  have h := product_perturbation_mem Finset.univ
    (fun i => U (σ i) i) (fun i => (1 : Matrix ι ι (MonicFrac A)) (σ i) i)
    (fun i _ => by by_cases hi : σ i = i <;> simp [Matrix.one_apply, hi])
    (fun i _ => hU (σ i) i)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · simpa [hs, Units.smul_def] using h
  · simpa [hs, Units.smul_def, sub_eq_add_neg, add_comm] using
      (properFractions (A := A)).neg_mem h

/-- A matrix whose polynomial part is the identity is invertible over the
actual monic localization. This step needs no locality assumption. -/
theorem isUnit_of_polynomialPart_eq_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : Matrix ι ι (MonicFrac A))
    (hU : U.map polynomialPart = (1 : Matrix ι ι A[X])) : IsUnit U := by
  apply (Matrix.isUnit_iff_isUnit_det U).mpr
  have hproper : U.det - 1 ∈ properFractions (A := A) := by
    apply det_sub_one_mem U
    intro i j
    change polynomialPart (U i j - (1 : Matrix ι ι (MonicFrac A)) i j) = 0
    have hij := congrFun (congrFun hU i) j
    by_cases h : i = j
    · subst j
      simpa [Matrix.one_apply, map_sub] using sub_eq_zero.mpr hij
    · simpa [Matrix.one_apply, h] using hij
  simpa using isUnit_one_add hproper

/-- If an `A`-submodule of finite polynomial vectors contains all multiples
of a fixed monic polynomial, its quotient is genuinely finite over `A`.
The proof exhibits surjective representatives of bounded degree. -/
theorem finite_quotient_of_monic_multiples {ι : Type*} [Fintype ι]
    (W : Submodule A (ι → A[X])) (h : A[X]) (hh : h.Monic)
    (hW : ∀ v : ι → A[X], (fun i => h * v i) ∈ W) :
    Module.Finite A ((ι → A[X]) ⧸ W) := by
  let inclusion : (ι → degreeLT A h.natDegree) →ₗ[A] (ι → A[X]) :=
    { toFun := fun v i => (v i).val
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  apply Module.Finite.of_surjective (W.mkQ.comp inclusion)
  intro a
  obtain ⟨v, rfl⟩ := W.mkQ_surjective a
  let r : ι → degreeLT A h.natDegree := fun i =>
    ⟨v i %ₘ h, mem_degreeLT.mpr (by
      rw [← degree_eq_natDegree hh.ne_zero]
      exact degree_modByMonic_lt (v i) hh)⟩
  refine ⟨r, ?_⟩
  apply (Submodule.Quotient.eq W).mpr
  have hw := W.neg_mem (hW (fun i => v i /ₘ h))
  convert hw using 1
  funext i
  change (v i %ₘ h) - v i = -(h * (v i /ₘ h))
  calc
    (v i %ₘ h) - v i = (v i %ₘ h) - ((v i %ₘ h) + h * (v i /ₘ h)) := by
      rw [modByMonic_add_div]
    _ = -(h * (v i /ₘ h)) := by abel

omit [Nontrivial A] in
/-- The precise Nakayama step for polynomial vectors: monic multiples
give a finite quotient, and generation modulo the maximal ideal forces
surjectivity. No finiteness hypothesis on the entire polynomial module
is incorrectly imposed. -/
theorem polynomialRange_eq_top [IsLocalRing A] {ι : Type*} [Fintype ι]
    (W : Submodule A (ι → A[X])) (h : A[X]) (hh : h.Monic)
    (hW : ∀ v : ι → A[X], (fun i => h * v i) ∈ W)
    (hmod : W ⊔ IsLocalRing.maximalIdeal A • (⊤ : Submodule A (ι → A[X])) = ⊤) :
    W = ⊤ := by
  have : Module.Finite A ((ι → A[X]) ⧸ W) := finite_quotient_of_monic_multiples W h hh hW
  have htop : (⊤ : Submodule A ((ι → A[X]) ⧸ W)) ≤
      IsLocalRing.maximalIdeal A • (⊤ : Submodule A ((ι → A[X]) ⧸ W)) := by
    have hm := congrArg (Submodule.map W.mkQ) hmod
    simpa only [Submodule.map_sup, Submodule.map_smul'', Submodule.mkQ_map_self,
      Submodule.map_top, Submodule.range_mkQ, bot_sup_eq] using hm.ge
  have hz : (⊤ : Submodule A ((ι → A[X]) ⧸ W)) = ⊥ :=
    Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ _ Module.Finite.fg_top htop
      (IsLocalRing.maximalIdeal_le_jacobson ⊥)
  apply top_unique
  intro v _
  apply (Submodule.Quotient.mk_eq_zero W).mp
  exact (Submodule.mem_bot A).mp (hz ▸ Submodule.mem_top (x := W.mkQ v))

end

end Decoupling.Horrocks
