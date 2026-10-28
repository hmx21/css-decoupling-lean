import Decoupling.Augmentation
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Quotient.Basic

/-!
# Linear maps into trivial translation modules

This file formalizes the constant-matrix evaluation step of Lemma III.2
and Appendix C in `notes/main.pdf`.  The target is the actual vector
space `𝔽₂ᵗ` with the `R` action restricted along augmentation, rather
than a new abstract module satisfying an annihilation hypothesis.

Every `R`-linear map `Rˢ → 𝔽₂ᵗ` has a unique constant matrix `C` and
sends `v` to `C v(1)`.  For an input matrix `H`, this map descends to
the actual cokernel of `H` exactly when `C H(1) = 0`.
-/

noncomputable section

namespace Decoupling.EvaluationLinear

open Matrix

/-- The coefficient field itself, with its augmentation-induced `R` action. -/
abbrev Coefficient : ModuleCat R :=
  (ModuleCat.restrictScalars augmentation).obj (ModuleCat.of (ZMod 2) (ZMod 2))

@[simp] theorem coefficient_smul (r : R) (a : Coefficient) :
    r • a = (augmentation r) • a := rfl

/-- Augmentation as a linear map into the actual trivial coefficient module. -/
def augmentationLinear : R →ₗ[R] Coefficient where
  toFun := augmentation
  map_add' := map_add augmentation
  map_smul' r s := map_mul augmentation r s

@[simp] theorem augmentationLinear_apply (r : R) : augmentationLinear r = augmentation r := rfl

theorem augmentationLinear_surjective : Function.Surjective augmentationLinear :=
  augmentation_surjective

theorem ker_augmentationLinear : LinearMap.ker augmentationLinear = J := by
  ext r
  change augmentation r = 0 ↔ r ∈ J
  rw [← ker_augmentation_eq_J]
  rfl

/-- The actual `𝔽₂ᵗ`, with translation acting through evaluation at `(1,1,1)`. -/
abbrev Trivial (t : ℕ) : ModuleCat R :=
  (ModuleCat.restrictScalars augmentation).obj (ModuleCat.of (ZMod 2) (Fin t → ZMod 2))

@[simp] theorem trivial_smul_apply {t : ℕ} (r : R) (v : Trivial t) (i : Fin t) :
    (r • v) i = augmentation r * v i := rfl

/-- A standard coordinate vector in the trivial module. -/
def trivialBasis {t : ℕ} (j : Fin t) : Trivial t := Pi.single j 1

/-- Entrywise evaluation of a matrix at `x = y = z = 1`. -/
def atOne {m n : ℕ} (H : Matrix (Fin m) (Fin n) R) :
    Matrix (Fin m) (Fin n) (ZMod 2) := H.map augmentation

@[simp] theorem atOne_apply {m n : ℕ} (H : Matrix (Fin m) (Fin n) R)
    (i : Fin m) (j : Fin n) : atOne H i j = augmentation (H i j) := rfl

/-- The `R`-linear map `v ↦ C v(1)`. -/
def evalMatrix {s t : ℕ} (C : Matrix (Fin t) (Fin s) (ZMod 2)) :
    (Fin s → R) →ₗ[R] Trivial t where
  toFun v := C *ᵥ (augmentation ∘ v)
  map_add' v w := by
    funext i
    change (∑ j, C i j * augmentation (v j + w j)) =
      (∑ j, C i j * augmentation (v j)) + ∑ j, C i j * augmentation (w j)
    simp [mul_add, Finset.sum_add_distrib]
  map_smul' r v := by
    funext i
    change (∑ j, C i j * augmentation (r * v j)) =
      augmentation r * ∑ j, C i j * augmentation (v j)
    simp [map_mul, Finset.mul_sum, mul_left_comm]

@[simp] theorem evalMatrix_apply {s t : ℕ} (C : Matrix (Fin t) (Fin s) (ZMod 2))
    (v : Fin s → R) : evalMatrix C v = C *ᵥ (augmentation ∘ v) := rfl

@[simp] theorem evalMatrix_single {s t : ℕ}
    (C : Matrix (Fin t) (Fin s) (ZMod 2)) (j : Fin s) :
    evalMatrix C (Pi.single j 1) = fun i => C i j := by
  funext i
  change (C *ᵥ (augmentation ∘ Pi.single j 1)) i = C i j
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- The constant matrix whose columns are the images of the standard basis. -/
def coefficientMatrix {s t : ℕ} (f : (Fin s → R) →ₗ[R] Trivial t) :
    Matrix (Fin t) (Fin s) (ZMod 2) := fun i j => f (Pi.single j 1) i

@[simp] theorem coefficientMatrix_evalMatrix {s t : ℕ}
    (C : Matrix (Fin t) (Fin s) (ZMod 2)) : coefficientMatrix (evalMatrix C) = C := by
  funext i j
  exact congrFun (evalMatrix_single C j) i

/-- Every linear map into the trivial translation module is constant-matrix evaluation. -/
@[simp] theorem evalMatrix_coefficientMatrix {s t : ℕ}
    (f : (Fin s → R) →ₗ[R] Trivial t) : evalMatrix (coefficientMatrix f) = f := by
  apply (Pi.basisFun R (Fin s)).ext
  intro j
  simp only [Pi.basisFun_apply]
  funext i
  exact congrFun (evalMatrix_single (coefficientMatrix f) j) i

/-- Uniquely parameterize all such `R`-linear maps by matrices over `𝔽₂`. -/
def evaluationEquiv (s t : ℕ) :
    Matrix (Fin t) (Fin s) (ZMod 2) ≃ ((Fin s → R) →ₗ[R] Trivial t) where
  toFun := evalMatrix
  invFun := coefficientMatrix
  left_inv := coefficientMatrix_evalMatrix
  right_inv := evalMatrix_coefficientMatrix

@[simp] theorem evalMatrix_zero {s t : ℕ} :
    evalMatrix (0 : Matrix (Fin t) (Fin s) (ZMod 2)) = 0 := by
  apply LinearMap.ext
  intro v
  funext i
  change ((0 : Matrix (Fin t) (Fin s) (ZMod 2)) *ᵥ (augmentation ∘ v)) i = 0
  simp

theorem evalMatrix_eq_zero_iff {s t : ℕ} (C : Matrix (Fin t) (Fin s) (ZMod 2)) :
    evalMatrix C = 0 ↔ C = 0 := by
  rw [← evalMatrix_zero]
  exact (evaluationEquiv s t).injective.eq_iff

/-- Evaluate a matrix composite: `C (H v)(1) = (C H(1)) v(1)`. -/
theorem evalMatrix_mulVec {q s t : ℕ}
    (C : Matrix (Fin t) (Fin s) (ZMod 2)) (H : Matrix (Fin s) (Fin q) R)
    (v : Fin q → R) : evalMatrix C (H *ᵥ v) = evalMatrix (C * atOne H) v := by
  change C *ᵥ (augmentation ∘ (H *ᵥ v)) =
    (C * H.map augmentation) *ᵥ (augmentation ∘ v)
  rw [← Matrix.mulVec_mulVec]
  congr 1
  funext i
  exact augmentation.map_mulVec H v i

theorem evalMatrix_comp_mulVecLin {q s t : ℕ}
    (C : Matrix (Fin t) (Fin s) (ZMod 2)) (H : Matrix (Fin s) (Fin q) R) :
    (evalMatrix C).comp H.mulVecLin = evalMatrix (C * atOne H) := by
  apply LinearMap.ext
  exact evalMatrix_mulVec C H

/-- The constant-matrix criterion for killing the column image of `H`. -/
theorem range_le_ker_evalMatrix_iff {q s t : ℕ}
    (C : Matrix (Fin t) (Fin s) (ZMod 2)) (H : Matrix (Fin s) (Fin q) R) :
    LinearMap.range H.mulVecLin ≤ LinearMap.ker (evalMatrix C) ↔ C * atOne H = 0 := by
  rw [LinearMap.range_le_ker_iff, evalMatrix_comp_mulVecLin, evalMatrix_eq_zero_iff]

/-- The concrete cokernel of the supplied presentation matrix. -/
abbrev Cokernel {q s : ℕ} (H : Matrix (Fin s) (Fin q) R) :=
  (Fin s → R) ⧸ LinearMap.range H.mulVecLin

/-- The quotient map induced by a solution of `C H(1) = 0`. -/
def descendEvalMatrix {q s t : ℕ}
    (C : Matrix (Fin t) (Fin s) (ZMod 2)) (H : Matrix (Fin s) (Fin q) R)
    (h : C * atOne H = 0) : Cokernel H →ₗ[R] Trivial t :=
  (LinearMap.range H.mulVecLin).liftQ (evalMatrix C)
    ((range_le_ker_evalMatrix_iff C H).mpr h)

@[simp] theorem descendEvalMatrix_mk {q s t : ℕ}
    (C : Matrix (Fin t) (Fin s) (ZMod 2)) (H : Matrix (Fin s) (Fin q) R)
    (h : C * atOne H = 0) (v : Fin s → R) :
    descendEvalMatrix C H h ((LinearMap.range H.mulVecLin).mkQ v) = evalMatrix C v := rfl

/-- Descent to the actual quotient is equivalent to the constant-matrix equation. -/
theorem exists_descent_iff {q s t : ℕ}
    (C : Matrix (Fin t) (Fin s) (ZMod 2)) (H : Matrix (Fin s) (Fin q) R) :
    (∃ f : Cokernel H →ₗ[R] Trivial t,
      f.comp (LinearMap.range H.mulVecLin).mkQ = evalMatrix C) ↔ C * atOne H = 0 := by
  constructor
  · rintro ⟨f, hf⟩
    apply (range_le_ker_evalMatrix_iff C H).mp
    rintro _ ⟨v, rfl⟩
    change evalMatrix C (H.mulVecLin v) = 0
    rw [← hf]
    change f ((LinearMap.range H.mulVecLin).mkQ (H.mulVecLin v)) = 0
    have hz : (LinearMap.range H.mulVecLin).mkQ (H.mulVecLin v) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩
    rw [hz, map_zero]
  · intro h
    refine ⟨descendEvalMatrix C H h, ?_⟩
    exact (LinearMap.range H.mulVecLin).liftQ_mkQ _ _

/-- If the columns of `T` lift an inclusion with a retraction `p`, the
constant matrix for `p` satisfies the second normalization equation `C T(1)=I`. -/
theorem retraction_matrix_equation {q s t : ℕ}
    (H : Matrix (Fin s) (Fin q) R)
    (p : Cokernel H →ₗ[R] Trivial t) (ι : Trivial t →ₗ[R] Cokernel H)
    (T : Matrix (Fin s) (Fin t) R)
    (hretraction : p.comp ι = LinearMap.id)
    (hlifts : ∀ j : Fin t,
      (LinearMap.range H.mulVecLin).mkQ (T *ᵥ Pi.single j 1) = ι (Pi.single j 1)) :
    coefficientMatrix (p.comp (LinearMap.range H.mulVecLin).mkQ) * atOne T = 1 := by
  let C := coefficientMatrix (p.comp (LinearMap.range H.mulVecLin).mkQ)
  have hcolumn (j : Fin t) :
      evalMatrix (C * atOne T) (Pi.single j 1) = (Pi.single j 1 : Trivial t) := by
    rw [← evalMatrix_mulVec C T]
    rw [show evalMatrix C = p.comp (LinearMap.range H.mulVecLin).mkQ from
      evalMatrix_coefficientMatrix _]
    change p ((LinearMap.range H.mulVecLin).mkQ (T *ᵥ Pi.single j 1)) =
      (Pi.single j 1 : Trivial t)
    rw [hlifts j]
    exact DFunLike.congr_fun hretraction _
  funext i j
  have h := congrFun (hcolumn j) i
  simpa only [evalMatrix_single, Pi.single_apply, Matrix.one_apply, eq_comm] using h

/-- An `R`-linear map out of `𝔽₂ᵗ` is determined by its values on its usual vector-space basis. -/
theorem linearMap_ext_trivial {t : ℕ} {N : Type*} [AddCommGroup N] [Module R N]
    {f g : Trivial t →ₗ[R] N}
    (h : ∀ j : Fin t, f (Pi.single j 1) = g (Pi.single j 1)) : f = g := by
  apply LinearMap.ext
  intro v
  have hv : v = ∑ j, constant (v j) • trivialBasis j := by
    funext i
    change v i = (∑ j : Fin t, fun k : Fin t => augmentation (constant (v j)) *
      (Pi.single (M := fun _ : Fin t => ZMod 2) j 1) k) i
    simp only [Finset.sum_apply, augmentation_constant, Pi.single_apply,
      mul_ite, mul_one, mul_zero]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · simp
  have hb (j : Fin t) : f (trivialBasis j) = g (trivialBasis j) := h j
  calc
    f v = f (∑ j, constant (v j) • trivialBasis j) := congrArg f hv
    _ = ∑ j, constant (v j) • f (trivialBasis j) := by simp only [map_sum, map_smul]
    _ = ∑ j, constant (v j) • g (trivialBasis j) := by simp only [hb]
    _ = g (∑ j, constant (v j) • trivialBasis j) := by
      simp only [map_sum, map_smul]
    _ = g v := congrArg g hv.symm

/-- The two constant-matrix equations give an actual retraction of the lifted inclusion. -/
theorem descend_retraction {q s t : ℕ}
    (C : Matrix (Fin t) (Fin s) (ZMod 2)) (H : Matrix (Fin s) (Fin q) R)
    (ι : Trivial t →ₗ[R] Cokernel H) (T : Matrix (Fin s) (Fin t) R)
    (hH : C * atOne H = 0) (hT : C * atOne T = 1)
    (hlifts : ∀ j : Fin t,
      (LinearMap.range H.mulVecLin).mkQ (T *ᵥ Pi.single j 1) = ι (Pi.single j 1)) :
    (descendEvalMatrix C H hH).comp ι = LinearMap.id := by
  apply linearMap_ext_trivial
  intro j
  change descendEvalMatrix C H hH (ι (Pi.single j 1)) = (Pi.single j 1 : Trivial t)
  rw [← hlifts j, descendEvalMatrix_mk, evalMatrix_mulVec, hT]
  funext i
  have h := congrFun (evalMatrix_single (1 : Matrix (Fin t) (Fin t) (ZMod 2)) j) i
  simpa only [Pi.single_apply, Matrix.one_apply, eq_comm] using h

/-- The supplied inclusion admits a retraction exactly when the two finite
linear equations `C H(1)=0` and `C T(1)=I` have a solution. -/
theorem exists_retraction_iff {q s t : ℕ}
    (H : Matrix (Fin s) (Fin q) R) (ι : Trivial t →ₗ[R] Cokernel H)
    (T : Matrix (Fin s) (Fin t) R)
    (hlifts : ∀ j : Fin t,
      (LinearMap.range H.mulVecLin).mkQ (T *ᵥ Pi.single j 1) = ι (Pi.single j 1)) :
    (∃ p : Cokernel H →ₗ[R] Trivial t, p.comp ι = LinearMap.id) ↔
      ∃ C : Matrix (Fin t) (Fin s) (ZMod 2), C * atOne H = 0 ∧ C * atOne T = 1 := by
  constructor
  · rintro ⟨p, hp⟩
    let C := coefficientMatrix (p.comp (LinearMap.range H.mulVecLin).mkQ)
    refine ⟨C, ?_, retraction_matrix_equation H p ι T hp hlifts⟩
    apply (exists_descent_iff C H).mp
    exact ⟨p, (evalMatrix_coefficientMatrix _).symm⟩
  · rintro ⟨C, hH, hT⟩
    exact ⟨descendEvalMatrix C H hH, descend_retraction C H ι T hH hT hlifts⟩

end Decoupling.EvaluationLinear
