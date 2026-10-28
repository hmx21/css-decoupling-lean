import Decoupling.Koszul

/-!
# Exactness of the three-generator Koszul complex

This file proves the elimination argument behind the Koszul resolution in
Proposition I.3 of `notes/main.pdf`. The matrices and basis order are those of
`Decoupling.Koszul`, so degree two is ordered `(yz,zx,xy)`.

`RegularTriple` contains explicit cancellation hypotheses expressing weak
regularity of `(u,v,w)`: multiplication by `u` is injective, multiplication by
`v` is injective modulo `(u)`, and multiplication by `w` is injective modulo
`(u,v)`. It does not assume a Koszul homology or exactness conclusion.

This generic elimination theorem takes the cancellation hypotheses as input.
`LaurentRegular` proves them for the manuscript's concrete Laurent ring.
-/

namespace Decoupling.Koszul

open Matrix

variable {A : Type*} [CommRing A] [CharP A 2]

/-- Explicit weak regularity, phrased as cancellation modulo the preceding
generators. The coefficients witnessing ideal membership are part of the
premise, rather than any assumptions about Koszul cycles or boundaries. -/
structure RegularTriple (u v w : A) : Prop where
  u_injective : Function.Injective (fun a : A => u * a)
  v_mod_u : ∀ a b : A, v * a = u * b → ∃ r : A, a = u * r
  w_mod_uv : ∀ a b c : A, w * a = u * b + v * c →
    ∃ r s : A, a = u * r + v * s

omit [CharP A 2] in
/-- A concrete route to the cancellation hypotheses: evaluate away the
preceding variables into domains, and identify the two evaluation kernels.
Neither kernel hypothesis is a Koszul exactness hypothesis. -/
theorem RegularTriple.of_evaluations {B C : Type*} [CommRing B] [CommRing C]
    [NoZeroDivisors B] [NoZeroDivisors C]
    (u v w : A) (hu : Function.Injective (fun a : A => u * a))
    (π : A →+* B) (σ : A →+* C)
    (hπu : π u = 0) (hπv : π v ≠ 0)
    (hσu : σ u = 0) (hσv : σ v = 0) (hσw : σ w ≠ 0)
    (hkerπ : ∀ a : A, π a = 0 → ∃ r : A, a = u * r)
    (hkerσ : ∀ a : A, σ a = 0 → ∃ r s : A, a = u * r + v * s) :
    RegularTriple u v w where
  u_injective := hu
  v_mod_u a b h := by
    have hprod : π v * π a = 0 := by simpa [hπu] using congrArg π h
    exact hkerπ a ((mul_eq_zero.mp hprod).resolve_left hπv)
  w_mod_uv a b c h := by
    have hprod : σ w * σ a = 0 := by simpa [hσu, hσv] using congrArg σ h
    exact hkerσ a ((mul_eq_zero.mp hprod).resolve_left hσw)

/-- Eliminate a degree-one cycle by first eliminating its last coordinate
modulo `(u,v)` and then its middle coordinate modulo `(u)`. -/
theorem first_syzygy (u v w : A) (hreg : RegularTriple u v w)
    (a b c : A) (h : u * a + v * b + w * c = 0) :
    ∃ p q r : A,
      a = w * q + v * r ∧ b = w * p + u * r ∧ c = v * p + u * q := by
  have hc : w * c = u * a + v * b := (CharTwo.add_eq_zero.mp h).symm
  obtain ⟨q, p, hcpq⟩ := hreg.w_mod_uv c a b hc
  have hab : u * (a + w * q) + v * (b + w * p) = 0 := by
    calc
      u * (a + w * q) + v * (b + w * p) =
          u * a + v * b + w * (u * q + v * p) := by ring
      _ = 0 := by rw [← hcpq]; exact h
  have hvb : v * (b + w * p) = u * (a + w * q) :=
    (CharTwo.add_eq_zero.mp hab).symm
  obtain ⟨r, hbr⟩ := hreg.v_mod_u (b + w * p) (a + w * q) hvb
  have har : a + w * q = v * r := hreg.u_injective (by
    calc
      u * (a + w * q) = v * (b + w * p) := hvb.symm
      _ = v * (u * r) := by rw [hbr]
      _ = u * (v * r) := by ring)
  refine ⟨p, q, r, ?_, ?_, ?_⟩
  · exact (CharTwo.add_eq_iff_eq_add.mp har).trans (add_comm _ _)
  · exact (CharTwo.add_eq_iff_eq_add.mp hbr).trans (add_comm _ _)
  · exact hcpq.trans (add_comm _ _)

/-- Eliminate a degree-two cycle. Only the first two regularity hypotheses
are needed in this degree. -/
theorem second_syzygy (u v w : A)
    (hu : Function.Injective (fun a : A => u * a))
    (hv : ∀ a b : A, v * a = u * b → ∃ r : A, a = u * r)
    (a b c : A) (h₂ : w * a + u * c = 0) (h₃ : v * a + u * b = 0) :
    ∃ r : A, a = u * r ∧ b = v * r ∧ c = w * r := by
  obtain ⟨r, har⟩ := hv a b (CharTwo.add_eq_zero.mp h₃)
  refine ⟨r, har, hu ?_, hu ?_⟩
  · calc
      u * b = v * a := (CharTwo.add_eq_zero.mp h₃).symm
      _ = v * (u * r) := by rw [har]
      _ = u * (v * r) := by ring
  · calc
      u * c = w * a := (CharTwo.add_eq_zero.mp h₂).symm
      _ = w * (u * r) := by rw [har]
      _ = u * (w * r) := by ring

/-- Exactness at `K₁`: `ker ∂₁ = im ∂₂`, in the manuscript's bases. -/
theorem exact_d₁_d₂ (u v w : A) (hreg : RegularTriple u v w)
    (a : Fin 3 → A) :
    d₁ u v w *ᵥ a = 0 ↔ ∃ b : Fin 3 → A, d₂ u v w *ᵥ b = a := by
  constructor
  · intro ha
    have h : u * a 0 + v * a 1 + w * a 2 = 0 := by
      have h₀ := congrFun ha 0
      simpa [d₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc] using h₀
    obtain ⟨p, q, r, ha₀, ha₁, ha₂⟩ := first_syzygy u v w hreg _ _ _ h
    refine ⟨![p, q, r], ?_⟩
    funext i
    fin_cases i <;>
      simp [d₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, ha₀, ha₁, ha₂]
  · rintro ⟨b, rfl⟩
    rw [Matrix.mulVec_mulVec, d₁_mul_d₂, Matrix.zero_mulVec]

/-- Exactness at `K₂`: `ker ∂₂ = im ∂₃`, in the manuscript's bases. -/
theorem exact_d₂_d₃ (u v w : A)
    (hu : Function.Injective (fun a : A => u * a))
    (hv : ∀ a b : A, v * a = u * b → ∃ r : A, a = u * r)
    (a : Fin 3 → A) :
    d₂ u v w *ᵥ a = 0 ↔ ∃ b : Fin 1 → A, d₃ u v w *ᵥ b = a := by
  constructor
  · intro ha
    have h₂ : w * a 0 + u * a 2 = 0 := by
      have h₁ := congrFun ha 1
      simpa [d₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h₁
    have h₃ : v * a 0 + u * a 1 = 0 := by
      have h₂ := congrFun ha 2
      simpa [d₂, Matrix.mulVec, dotProduct, Fin.sum_univ_succ] using h₂
    obtain ⟨r, ha₀, ha₁, ha₂⟩ := second_syzygy u v w hu hv _ _ _ h₂ h₃
    refine ⟨![r], ?_⟩
    funext i
    fin_cases i <;> simp [d₃, Matrix.mulVec, dotProduct, ha₀, ha₁, ha₂]
  · rintro ⟨b, rfl⟩
    rw [Matrix.mulVec_mulVec, d₂_mul_d₃, Matrix.zero_mulVec]

omit [CharP A 2] in
/-- Exactness at the left endpoint: `∂₃` is injective whenever `u` is a
non-zero-divisor. -/
theorem d₃_injective (u v w : A)
    (hu : Function.Injective (fun a : A => u * a)) :
    Function.Injective (fun a : Fin 1 → A => d₃ u v w *ᵥ a) := by
  intro a b h
  have h₀ : u * a 0 = u * b 0 := by
    simpa [d₃, Matrix.mulVec, dotProduct] using congrFun h 0
  funext i
  fin_cases i
  exact hu h₀

omit [CharP A 2] in
/-- The image of `∂₁` is exactly the ideal generated by its three entries.
This identifies the right endpoint of the augmented complex. -/
theorem image_d₁_iff (u v w r : A) :
    (∃ a : Fin 3 → A, d₁ u v w *ᵥ a = ![r]) ↔
      r ∈ Ideal.span ({u, v, w} : Set A) := by
  constructor
  · rintro ⟨a, ha⟩
    have hr : u * a 0 + v * a 1 + w * a 2 = r := by
      have h₀ := congrFun ha 0
      simpa [d₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, add_assoc] using h₀
    rw [← hr]
    exact Ideal.add_mem _
      (Ideal.add_mem _
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
        (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp))))
      (Ideal.mul_mem_right _ _ (Ideal.subset_span (by simp)))
  · intro hr
    obtain ⟨a, s, hs, hrs⟩ := Ideal.mem_span_insert.mp hr
    obtain ⟨b, c, hbc⟩ := Ideal.mem_span_pair.mp hs
    refine ⟨![a, b, c], ?_⟩
    funext i
    fin_cases i
    simp [d₁, Matrix.mulVec, dotProduct, Fin.sum_univ_succ, hrs, ← hbc]
    ring

end Decoupling.Koszul
