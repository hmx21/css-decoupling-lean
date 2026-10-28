import Decoupling.CSS
import Decoupling.LaurentRegular
import Decoupling.EvaluationLinear
import Mathlib.LinearAlgebra.Isomorphisms

/-!
# The two concrete toric windows

The check matrices, adjoint, coefficient ring, and basis order are those of
`notes/main.pdf`, Proposition I.3. Both topological conditions are proved
for each window. In particular the Z-sector exactness is proved, rather
than inferred merely from the X-sector chain condition.

The syndrome cokernels are identified by actual R-linear equivalences with
the trivial coefficient module `𝔽₂` and the augmentation ideal `J`.

`ToricExt` identifies both windows' genuine derived Ext groups using these
exactness results.
-/

namespace Decoupling.ToricWindows

open Matrix PhysicalKoszul

noncomputable section

/-- Coefficientwise Laurent conjugation of a vector. -/
def barVec {ι : Type*} (a : ι → R) : ι → R := fun i => bar (a i)

@[simp] theorem barVec_barVec {ι : Type*} (a : ι → R) : barVec (barVec a) = a := by
  funext i
  exact bar_bar _

@[simp] theorem barVec_zero {ι : Type*} : barVec (0 : ι → R) = 0 := by
  funext i
  exact bar_zero

theorem barVec_injective {ι : Type*} : Function.Injective (@barVec ι) := by
  intro a b h
  simpa using congrArg barVec h

@[simp] theorem barVec_eq_zero_iff {ι : Type*} (a : ι → R) :
    barVec a = 0 ↔ a = 0 := by
  constructor
  · intro h
    simpa using congrArg barVec h
  · rintro rfl
    exact barVec_zero

theorem barVec_mulVec {m n : Type*} [Fintype n]
    (A : Matrix m n R) (a : n → R) :
    barVec (A *ᵥ a) = A.map bar *ᵥ barVec a := by
  funext i
  exact RingHom.map_mulVec bar.toRingHom A a i

@[simp] theorem barVec_map_mulVec {m n : Type*} [Fintype n]
    (A : Matrix m n R) (a : n → R) :
    barVec (A.map bar *ᵥ a) = A *ᵥ barVec a := by
  rw [barVec_mulVec]
  congr 1
  funext i j
  exact bar_bar _

/-- Exactness is preserved by coefficientwise Laurent conjugation.
Conjugation is semilinear; no false R-linearity assertion is used here. -/
theorem conjugate_exactness {m n k : Type*} [Fintype n] [Fintype k]
    (A : Matrix m n R) (B : Matrix n k R)
    (h : ∀ a : n → R, A *ᵥ a = 0 ↔ ∃ b : k → R, B *ᵥ b = a)
    (a : n → R) :
    A.map bar *ᵥ a = 0 ↔ ∃ b : k → R, B.map bar *ᵥ b = a := by
  have hk : A.map bar *ᵥ a = 0 ↔ A *ᵥ barVec a = 0 := by
    rw [← barVec_eq_zero_iff (A.map bar *ᵥ a), barVec_map_mulVec]
  rw [hk, h]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨barVec b, ?_⟩
    rw [← barVec_mulVec, hb, barVec_barVec]
  · rintro ⟨b, hb⟩
    refine ⟨barVec b, ?_⟩
    simpa using congrArg barVec hb

theorem dagger_partial₁ : dagger partial₁ = partial₃.map bar := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem dagger_partial₂ : dagger partial₂ = partial₂.map bar := by
  funext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem dagger_partial₃ : dagger partial₃ = partial₁.map bar := by
  funext i j
  fin_cases i
  fin_cases j <;> rfl

/-- `TC₁` has physical qubits in `K₁`. -/
def TC₁ : CSS.Checks 3 1 3 where
  H_X := partial₁
  H_Z := dagger partial₂

/-- `TC₂` has physical qubits in `K₂`. -/
def TC₂ : CSS.Checks 3 3 1 where
  H_X := partial₂
  H_Z := dagger partial₃

/-- Both topological conditions for the first toric window. -/
theorem TC₁_topological : TC₁.Topological := by
  constructor
  · apply Submodule.ext
    intro a
    change partial₁ *ᵥ a = 0 ↔ ∃ b, dagger (dagger partial₂) *ᵥ b = a
    rw [dagger_dagger]
    exact exact_partial₁_partial₂ a
  · apply Submodule.ext
    intro a
    change dagger partial₂ *ᵥ a = 0 ↔ ∃ b, dagger partial₁ *ᵥ b = a
    rw [dagger_partial₂, dagger_partial₁]
    exact conjugate_exactness partial₂ partial₃ exact_partial₂_partial₃ a

/-- Both topological conditions for the second toric window. -/
theorem TC₂_topological : TC₂.Topological := by
  constructor
  · apply Submodule.ext
    intro a
    change partial₂ *ᵥ a = 0 ↔ ∃ b, dagger (dagger partial₃) *ᵥ b = a
    rw [dagger_dagger]
    exact exact_partial₂_partial₃ a
  · apply Submodule.ext
    intro a
    change dagger partial₃ *ᵥ a = 0 ↔ ∃ b, dagger partial₂ *ᵥ b = a
    rw [dagger_partial₃, dagger_partial₂]
    exact conjugate_exactness partial₁ partial₂ exact_partial₁_partial₂ a

/-- The augmentation `K₁ → J` is `∂₁`, with its one-dimensional target
identified with `R`. This is the map in Eq. (16). -/
def idealAugmentation : (Fin 3 → R) →ₗ[R] J :=
  LinearMap.codRestrict J
    ((LinearMap.proj 0).comp (Matrix.mulVecLin partial₁)) (by
      intro a
      apply (Koszul.image_d₁_iff u v w _).mp
      refine ⟨a, ?_⟩
      funext i
      fin_cases i
      rfl)

@[simp] theorem idealAugmentation_apply (a : Fin 3 → R) :
    (idealAugmentation a : R) = (partial₁ *ᵥ a) 0 := rfl

theorem idealAugmentation_surjective : Function.Surjective idealAugmentation := by
  intro r
  obtain ⟨a, ha⟩ := (Koszul.image_d₁_iff u v w r.val).mpr r.property
  refine ⟨a, Subtype.ext ?_⟩
  exact congrFun ha 0

theorem ker_idealAugmentation :
    LinearMap.ker idealAugmentation = LinearMap.range (Matrix.mulVecLin partial₂) := by
  apply Submodule.ext
  intro a
  change idealAugmentation a = 0 ↔ ∃ b, partial₂ *ᵥ b = a
  rw [← exact_partial₁_partial₂ a]
  constructor
  · intro h
    have h₀ : (partial₁ *ᵥ a) 0 = 0 := congrArg Subtype.val h
    funext i
    fin_cases i
    exact h₀
  · intro h
    apply Subtype.ext
    exact congrFun h 0

/-- The actual syndrome quotient of `TC₂` is R-linearly isomorphic to `J`.
Its forward map is induced by `∂₁`, exactly as in Eq. (16). -/
def TC₂_coker_equiv_J : TC₂.N ≃ₗ[R] J :=
  (Submodule.quotEquivOfEq _ _ ker_idealAugmentation.symm).trans
    (idealAugmentation.quotKerEquivOfSurjective idealAugmentation_surjective)

@[simp] theorem TC₂_coker_equiv_J_mk (a : Fin 3 → R) :
    (TC₂_coker_equiv_J (Submodule.Quotient.mk a) : R) = (partial₁ *ᵥ a) 0 := by
  rfl

/-- The augmentation of the first toric window, with its actual trivial
translation action on `𝔽₂`. -/
def coefficientAugmentation : (Fin 1 → R) →ₗ[R] EvaluationLinear.Coefficient :=
  EvaluationLinear.augmentationLinear.comp (LinearMap.proj 0)

@[simp] theorem coefficientAugmentation_apply (a : Fin 1 → R) :
    coefficientAugmentation a = augmentation (a 0) := rfl

theorem coefficientAugmentation_surjective : Function.Surjective coefficientAugmentation := by
  intro c
  obtain ⟨r, hr⟩ := EvaluationLinear.augmentationLinear_surjective c
  exact ⟨![r], hr⟩

theorem ker_coefficientAugmentation :
    LinearMap.ker coefficientAugmentation = LinearMap.range (Matrix.mulVecLin partial₁) := by
  apply Submodule.ext
  intro a
  change augmentation (a 0) = 0 ↔ ∃ b, partial₁ *ᵥ b = a
  have ha : ![a 0] = a := by
    funext i
    fin_cases i
    rfl
  simpa only [ha] using exact_augmentation (a 0)

/-- The actual syndrome quotient of `TC₁` is the coefficient field with
trivial translations, as an R-module. -/
def TC₁_coker_equiv_coefficient : TC₁.N ≃ₗ[R] EvaluationLinear.Coefficient :=
  (Submodule.quotEquivOfEq _ _ ker_coefficientAugmentation.symm).trans
    (coefficientAugmentation.quotKerEquivOfSurjective coefficientAugmentation_surjective)

@[simp] theorem TC₁_coker_equiv_coefficient_mk (a : Fin 1 → R) :
    TC₁_coker_equiv_coefficient (Submodule.Quotient.mk a) = augmentation (a 0) := by
  rfl

end

end Decoupling.ToricWindows
