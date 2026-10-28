import Decoupling.KoszulExact
import Decoupling.Augmentation
import Decoupling.PartialEvaluation
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Field.ZMod

/-!
# Concrete regularity obligations for the Laurent ring

The Laurent ring is a domain: its coefficient field is a domain and its
translation group `ℤ³` has unique sums. Together with the proved coordinate
evaluation kernels from `PartialEvaluation`, this discharges all the
cancellation hypotheses for the manuscript's sequence `(u,v,w)`.

The final theorem proves exactness at every term of the augmented sequence
`0 → R → R³ → R³ → R → 𝔽₂ → 0`. No regularity or exactness hypothesis
remains. `ToricExt` and `RestrictionExtVanishing` provide the categorical
resolution interfaces used to identify the genuine derived Ext groups.
-/

namespace Decoupling

noncomputable section

open Matrix

/-- Distinct translation exponents give distinct monomials. -/
theorem monomial_injective : Function.Injective monomial :=
  AddMonoidAlgebra.single_left_injective one_ne_zero

theorem translationBasis_ne_zero (i : Fin 3) : translationBasis i ≠ 0 := by
  intro h
  have h₀ := congrFun h i
  simp [translationBasis] at h₀

theorem monomial_sub_one_ne_zero {a : Translation} (ha : a ≠ 0) :
    monomial a - 1 ≠ 0 := by
  intro h
  apply ha
  apply monomial_injective
  simpa using sub_eq_zero.mp h

theorem u_ne_zero : u ≠ 0 := monomial_sub_one_ne_zero (translationBasis_ne_zero 0)
theorem v_ne_zero : v ≠ 0 := monomial_sub_one_ne_zero (translationBasis_ne_zero 1)
theorem w_ne_zero : w ≠ 0 := monomial_sub_one_ne_zero (translationBasis_ne_zero 2)

/-- The first regularity hypothesis over the actual Laurent ring. -/
theorem u_mul_injective : Function.Injective (fun a : R => u * a) :=
  fun _ _ h => mul_left_cancel₀ u_ne_zero h

/-- The concrete Laurent generators satisfy the three cancellation
hypotheses. The quotient regularity conditions are proved using the
coordinate-evaluation kernels, not assumed. -/
theorem laurent_regularTriple : Koszul.RegularTriple u v w := by
  apply Koszul.RegularTriple.of_evaluations u v w u_mul_injective
    PartialEvaluation.evalX PartialEvaluation.evalXY
    PartialEvaluation.evalX_u (by simpa using v_ne_zero)
    PartialEvaluation.evalXY_u PartialEvaluation.evalXY_v (by simpa using w_ne_zero)
  · intro a ha
    have ha' : a ∈ Ideal.span ({u} : Set R) := by
      rw [← PartialEvaluation.ker_evalX]
      exact RingHom.mem_ker.mpr ha
    exact Ideal.mem_span_singleton.mp ha'
  · intro a ha
    have ha' : a ∈ Ideal.span ({u, v} : Set R) := by
      rw [← PartialEvaluation.ker_evalXY]
      exact RingHom.mem_ker.mpr ha
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.mp ha'
    exact ⟨r, s, by simpa [mul_comm] using hrs.symm⟩

/-- The manuscript's concrete `∂₃` is injective, with no unproved regularity
assumptions. -/
theorem PhysicalKoszul.partial₃_injective :
    Function.Injective (fun a : Fin 1 → R => PhysicalKoszul.partial₃ *ᵥ a) :=
  Koszul.d₃_injective u v w u_mul_injective

/-- Exactness at `K₀ = R`: the augmentation kernel is the image of `∂₁`.
This uses the proved concrete augmentation-kernel theorem. -/
theorem PhysicalKoszul.exact_augmentation (r : R) :
    augmentation r = 0 ↔ ∃ a : Fin 3 → R, PhysicalKoszul.partial₁ *ᵥ a = ![r] := by
  rw [← RingHom.mem_ker, ker_augmentation_eq_J]
  exact (Koszul.image_d₁_iff u v w r).symm

/-- Exactness at `K₁` for the actual three-variable Laurent ring. -/
theorem PhysicalKoszul.exact_partial₁_partial₂ (a : Fin 3 → R) :
    PhysicalKoszul.partial₁ *ᵥ a = 0 ↔
      ∃ b : Fin 3 → R, PhysicalKoszul.partial₂ *ᵥ b = a :=
  Koszul.exact_d₁_d₂ u v w laurent_regularTriple a

/-- Exactness at `K₂` for the actual three-variable Laurent ring. -/
theorem PhysicalKoszul.exact_partial₂_partial₃ (a : Fin 3 → R) :
    PhysicalKoszul.partial₂ *ᵥ a = 0 ↔
      ∃ b : Fin 1 → R, PhysicalKoszul.partial₃ *ᵥ b = a :=
  Koszul.exact_d₂_d₃ u v w laurent_regularTriple.u_injective
    laurent_regularTriple.v_mod_u a

/-- Proposition I.3: exactness of every term in the augmented Koszul sequence
over the concrete Laurent ring. All cancellation hypotheses are discharged. -/
theorem PhysicalKoszul.augmented_sequence_exact :
    Function.Injective (fun a : Fin 1 → R => PhysicalKoszul.partial₃ *ᵥ a) ∧
    (∀ a : Fin 3 → R, PhysicalKoszul.partial₂ *ᵥ a = 0 ↔
      ∃ b : Fin 1 → R, PhysicalKoszul.partial₃ *ᵥ b = a) ∧
    (∀ a : Fin 3 → R, PhysicalKoszul.partial₁ *ᵥ a = 0 ↔
      ∃ b : Fin 3 → R, PhysicalKoszul.partial₂ *ᵥ b = a) ∧
    (∀ r : R, augmentation r = 0 ↔
      ∃ a : Fin 3 → R, PhysicalKoszul.partial₁ *ᵥ a = ![r]) ∧
    Function.Surjective augmentation :=
  ⟨PhysicalKoszul.partial₃_injective, PhysicalKoszul.exact_partial₂_partial₃,
    PhysicalKoszul.exact_partial₁_partial₂, PhysicalKoszul.exact_augmentation,
    augmentation_surjective⟩

end

end Decoupling
