import Decoupling.HighDim.PauliUnitary
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Genuine qudit product-state ancillas

Source: `drafts/main.tex`, Section IV.B, the |0⟩ and |+⟩ ancillas.
Their explicitly normalized complex states are characterized by their complete
simultaneous Pauli fixed spaces, including the empty-site case. No restriction
to characteristic two is made. Exactness of disk stabilization is a separate
algebraic result and is not inferred from the Hilbert-space statements here.
-/

noncomputable section
namespace Decoupling.HighDim.PauliUnitary
open Matrix
variable {p : ℕ} [NeZero p]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The all-zero computational auxiliary state. -/
def zeroState : State p ι := ket 0

/-- The normalized uniform superposition, the tensor product of |+⟩ states. -/
def plusState : State p ι :=
  fun _ => ((Real.sqrt (Fintype.card (Config p ι) : ℝ))⁻¹ : ℂ)

theorem Z_zeroState (b : Config p ι) : Z b *ᵥ zeroState = zeroState := by
  simpa [zeroState] using Z_ket b (0 : Config p ι)

theorem X_plusState (a : Config p ι) : X a *ᵥ plusState = plusState := by
  funext s
  rw [X_apply]
  rfl

theorem zeroState_norm : ‖WithLp.toLp 2 (zeroState (p := p) (ι := ι))‖ = 1 := by
  change ‖(EuclideanSpace.single (0 : Config p ι) (1 : ℂ))‖ = 1
  simp

theorem plusState_norm : ‖WithLp.toLp 2 (plusState (p := p) (ι := ι))‖ = 1 := by
  have hc : (0 : ℝ) < Fintype.card (Config p ι) := by exact_mod_cast Fintype.card_pos
  rw [EuclideanSpace.norm_eq]
  simp only [plusState, norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, inv_pow]
  rw [Real.sq_sqrt hc.le, mul_inv_cancel₀ (ne_of_gt hc), Real.sqrt_one]

/-- Invariance under all X supports is exactly constant computational amplitude. -/
theorem all_X_fixed_iff (ψ : State p ι) :
    (∀ a, X a *ᵥ ψ = ψ) ↔ ∀ s, ψ s = ψ 0 := by
  constructor
  · intro h s
    simpa only [X_apply, zero_sub, neg_neg] using congrFun (h (-s)) 0
  · intro h a
    funext s
    rw [X_apply, h (s - a), h s]

/-- Invariance under all Z supports is exactly support at the zero configuration. -/
theorem all_Z_fixed_iff (ψ : State p ι) :
    (∀ b, Z b *ᵥ ψ = ψ) ↔ ∀ s, s ≠ 0 → ψ s = 0 := by
  constructor
  · intro h s hs
    obtain ⟨i, hi⟩ : ∃ i, s i ≠ 0 := by
      by_contra! hh
      exact hs (funext hh)
    have hphase : phase (s i) ≠ 1 := fun hh => hi ((phase_eq_one _).mp hh)
    have hz := congrFun (h (Pi.single i 1)) s
    simp only [Z_apply, single_dotProduct, one_mul] at hz
    have hh : (phase (s i) - 1) * ψ s = 0 := by rw [sub_mul, one_mul, hz, sub_self]
    exact (mul_eq_zero.mp hh).resolve_left (sub_ne_zero.mpr hphase)
  · intro h b
    funext s
    by_cases hs : s = 0
    · subst s
      simp [Z_apply]
    · simp [Z_apply, h s hs]

/-- Actual simultaneous +1 eigenspace of the pure X checks. -/
def fixedX : Submodule ℂ (State p ι) where
  carrier := {ψ | ∀ a, X a *ᵥ ψ = ψ}
  zero_mem' := by intro a; simp
  add_mem' := by intro ψ χ hψ hχ a; rw [Matrix.mulVec_add, hψ a, hχ a]
  smul_mem' := by intro c ψ hψ a; rw [Matrix.mulVec_smul, hψ a]

/-- Actual simultaneous +1 eigenspace of the pure Z checks. -/
def fixedZ : Submodule ℂ (State p ι) where
  carrier := {ψ | ∀ b, Z b *ᵥ ψ = ψ}
  zero_mem' := by intro b; simp
  add_mem' := by intro ψ χ hψ hχ b; rw [Matrix.mulVec_add, hψ b, hχ b]
  smul_mem' := by intro c ψ hψ b; rw [Matrix.mulVec_smul, hψ b]

theorem plus_amplitude_ne_zero : plusState (p := p) (ι := ι) 0 ≠ 0 := by
  have hc : (0 : ℝ) < Fintype.card (Config p ι) := by exact_mod_cast Fintype.card_pos
  change ((Real.sqrt (Fintype.card (Config p ι) : ℝ) : ℂ))⁻¹ ≠ 0
  apply inv_ne_zero
  exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr hc)

theorem plusState_ne_zero : (plusState : State p ι) ≠ 0 := by
  intro h
  exact plus_amplitude_ne_zero (congrFun h 0)

omit [NeZero p] [DecidableEq ι] in
theorem zeroState_ne_zero : (zeroState : State p ι) ≠ 0 := by
  intro h
  have hh := congrFun h 0
  simp [zeroState, ket] at hh

/-- Identity-X checks fix precisely the all-plus line, not merely one vector on it. -/
theorem fixedX_eq_span : (fixedX : Submodule ℂ (State p ι)) =
    Submodule.span ℂ {plusState} := by
  ext ψ
  change (∀ a, X a *ᵥ ψ = ψ) ↔ ψ ∈ Submodule.span ℂ {plusState}
  rw [all_X_fixed_iff, Submodule.mem_span_singleton]
  constructor
  · intro h
    refine ⟨ψ 0 / plusState (p := p) (ι := ι) 0, ?_⟩
    funext s
    change (ψ 0 / plusState (p := p) (ι := ι) 0) * plusState s = ψ s
    change (ψ 0 / plusState (p := p) (ι := ι) 0) * plusState (p := p) (ι := ι) 0 = ψ s
    rw [div_mul_cancel₀ _ plus_amplitude_ne_zero, h s]
  · rintro ⟨c, rfl⟩ s
    rfl

/-- Identity-Z checks fix precisely the all-zero computational line. -/
theorem fixedZ_eq_span : (fixedZ : Submodule ℂ (State p ι)) =
    Submodule.span ℂ {zeroState} := by
  ext ψ
  change (∀ b, Z b *ᵥ ψ = ψ) ↔ ψ ∈ Submodule.span ℂ {zeroState}
  rw [all_Z_fixed_iff, Submodule.mem_span_singleton]
  constructor
  · intro h
    refine ⟨ψ 0, ?_⟩
    funext s
    by_cases hs : s = 0
    · subst s
      simp [zeroState, ket]
    · simp [zeroState, ket, hs, h s hs]
  · rintro ⟨c, rfl⟩ s hs
    simp [zeroState, ket, hs]

theorem fixedX_finrank : Module.finrank ℂ (fixedX (p := p) (ι := ι)) = 1 := by
  rw [fixedX_eq_span]
  exact finrank_span_singleton plusState_ne_zero

theorem fixedZ_finrank : Module.finrank ℂ (fixedZ (p := p) (ι := ι)) = 1 := by
  rw [fixedZ_eq_span]
  exact finrank_span_singleton zeroState_ne_zero

end Decoupling.HighDim.PauliUnitary
