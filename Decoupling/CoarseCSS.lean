import Decoupling.RestrictionDuality
import Decoupling.RetainedLayers
import Decoupling.ResolutionExt

/-!
# Actual CSS checks on the retained lattice

The residue basis of the literal subring for nℤ³ expands each physical matrix.
Renaming retained translations and enumerating the residue coordinates produces
ordinary `CSS.Checks` over the manuscript's Laurent ring. The adjoint, both
physical exactness equalities, and a supplied free resolution are transported.
-/

namespace Decoupling.CoarseCSS

open GeneralRetained RestrictionDuality Matrix

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (n : ℕ) [NeZero n]

abbrev Index (k : ℕ) := Fin k × Residue n

def size (k : ℕ) : ℕ := Fintype.card (Index n k)

omit [NeZero n] in
@[simp] theorem size_eq (k : ℕ) : size n k = k * n ^ 3 := by
  simp [size, Index, Residue]

def indexEquiv (k : ℕ) : Index n k ≃ Fin (size n k) := Fintype.equivFin _

abbrev RetainedVector (k : ℕ) :=
  RetainedLayers.restricted n (ModuleCat.of R (Fin k → R))

/-- Coordinates are first expanded in S, then the retained variables are renamed. -/
def vector {k : ℕ} (v : Fin k → R) : Fin (size n k) → R :=
  fun i => (renameEquiv n).symm (expandVector n v ((indexEquiv n k).symm i))

/-- Actual changed translation action on the source, with no new module postulate. -/
def vectorEquiv (k : ℕ) : RetainedVector n k ≃ₗ[R] (Fin (size n k) → R) where
  toFun := vector n
  invFun v := (RestrictionDuality.vectorEquiv n (Fin k)).symm
    (fun i => renameEquiv n (v (indexEquiv n k i)))
  map_add' v w := by
    change vector n ((show Fin k → R from v) + (show Fin k → R from w)) = _
    funext i
    simp [vector, expandVector]
  map_smul' r v := by
    funext i
    change (renameEquiv n).symm ((residueBasis n).coord
      ((indexEquiv n k).symm i).2
      (embed n r * v ((indexEquiv n k).symm i).1)) = _
    have hr : embed n r = algebraMap (S n) R (renameEquiv n r) := rfl
    rw [hr, ← Algebra.smul_def, map_smul]
    simp [vector, expandVector]
  left_inv v := by
    apply (RestrictionDuality.vectorEquiv n (Fin k)).injective
    rw [LinearEquiv.apply_symm_apply]
    funext i
    simp only [vector, Equiv.symm_apply_apply, RingEquiv.apply_symm_apply]
    rfl
  right_inv v := by
    funext i
    simp [vector, ← RestrictionDuality.vectorEquiv_apply]

@[simp] theorem vectorEquiv_apply {k : ℕ} (v : RetainedVector n k) :
    vectorEquiv n k v = vector n v := rfl

@[simp] theorem vector_zero {k : ℕ} : vector n (0 : Fin k → R) = 0 :=
  (vectorEquiv n k).map_zero

/-- The check matrices have ordinary finite numerical row/column dimensions. -/
def matrix {m k : ℕ} (D : Matrix (Fin m) (Fin k) R) :
    Matrix (Fin (size n m)) (Fin (size n k)) R :=
  ((expandMatrix n D).map (renameEquiv n).symm).submatrix
    (indexEquiv n m).symm (indexEquiv n k).symm

@[simp] theorem matrix_zero {m k : ℕ} : matrix n (0 : Matrix (Fin m) (Fin k) R) = 0 := by
  funext i j
  simp [matrix]

@[simp] theorem matrix_one {k : ℕ} : matrix n (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  simp [matrix]

theorem matrix_mul {m k l : ℕ} (D : Matrix (Fin m) (Fin k) R)
    (E : Matrix (Fin k) (Fin l) R) : matrix n (D * E) = matrix n D * matrix n E := by
  simp only [matrix, expandMatrix_mul, Matrix.map_mul, submatrix_mul_equiv]

theorem rename_bar (s : S n) : (renameEquiv n).symm (barS n s) =
    bar ((renameEquiv n).symm s) := by
  simp [barS]

theorem matrix_dagger {m k : ℕ} (D : Matrix (Fin m) (Fin k) R) :
    matrix n (dagger D) = dagger (matrix n D) := by
  funext i j
  simp only [matrix, expandMatrix_dagger, submatrix_apply, Matrix.map_apply,
    daggerS, dagger_apply, rename_bar]

/-- Expansion intertwines the original and retained physical maps. -/
theorem matrix_mulVec {m k : ℕ} (D : Matrix (Fin m) (Fin k) R) (v : Fin k → R) :
    matrix n D *ᵥ vector n v = vector n (D *ᵥ v) := by
  rw [matrix, submatrix_mulVec_equiv]
  have hv : vector n v ∘ indexEquiv n k =
      (renameEquiv n).symm ∘ expandVector n v := by
    funext i
    simp [vector]
  rw [Equiv.symm_symm, hv]
  funext i
  change (_ *ᵥ ((renameEquiv n).symm ∘ expandVector n v)) _ = _
  have hm := RingHom.map_mulVec (renameEquiv n).symm.toRingHom
    (expandMatrix n D) (expandVector n v) ((indexEquiv n m).symm i)
  exact hm.symm.trans (by rw [expandMatrix_mulVec]; rfl)

theorem exactness_preserved {m k l : ℕ} (D : Matrix (Fin m) (Fin k) R)
    (E : Matrix (Fin k) (Fin l) R)
    (h : ∀ v, D *ᵥ v = 0 ↔ ∃ z, E *ᵥ z = v) :
    ∀ v, matrix n D *ᵥ v = 0 ↔ ∃ z, matrix n E *ᵥ z = v := by
  intro v
  obtain ⟨v, rfl⟩ := (vectorEquiv n k).surjective v
  change matrix n D *ᵥ vector n v = 0 ↔ _
  rw [matrix_mulVec]
  change vectorEquiv n m (D *ᵥ v) = 0 ↔ _
  rw [(vectorEquiv n m).map_eq_zero_iff, h]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨vector n z, matrix_mulVec n E z⟩
  · rintro ⟨z, hz⟩
    obtain ⟨z, rfl⟩ := (vectorEquiv n l).surjective z
    refine ⟨z, (vectorEquiv n k).injective ?_⟩
    simpa only [vectorEquiv_apply, matrix_mulVec] using hz

def checks {q s r : ℕ} (c : CSS.Checks q s r) :
    CSS.Checks (size n q) (size n s) (size n r) where
  H_X := matrix n c.H_X
  H_Z := matrix n c.H_Z

theorem topological {q s r : ℕ} (c : CSS.Checks q s r) (h : c.Topological) :
    (checks n c).Topological := by
  constructor
  · ext v
    change matrix n c.H_X *ᵥ v = 0 ↔ ∃ z, dagger (matrix n c.H_Z) *ᵥ z = v
    rw [← matrix_dagger]
    exact exactness_preserved n _ _ (c.exact_X h) v
  · ext v
    change matrix n c.H_Z *ᵥ v = 0 ↔ ∃ z, dagger (matrix n c.H_X) *ᵥ z = v
    rw [← matrix_dagger]
    exact exactness_preserved n _ _ (c.exact_Z h) v

/-- The retained CSS presentation has an actual transported free resolution. -/
def resolution {q s r cX : ℕ} {c : CSS.Checks q s r}
    (h : ResolutionExt.CSSResolution c cX) :
    ResolutionExt.CSSResolution (checks n c) (size n cX) where
  Γ := matrix n h.Γ
  zero := by
    change dagger (matrix n c.H_X) * matrix n h.Γ = 0
    rw [← matrix_dagger, ← matrix_mul, h.zero, matrix_zero]
  exact₁ := by
    change ∀ a, dagger (matrix n c.H_X) *ᵥ a = 0 ↔ ∃ b, matrix n h.Γ *ᵥ b = a
    rw [← matrix_dagger]
    exact exactness_preserved n _ _ h.exact₁
  injectiveΓ := by
    intro a b hab
    obtain ⟨a, rfl⟩ := (vectorEquiv n cX).surjective a
    obtain ⟨b, rfl⟩ := (vectorEquiv n cX).surjective b
    have h' : h.Γ *ᵥ a = h.Γ *ᵥ b := (vectorEquiv n s).injective (by
      simpa only [vectorEquiv_apply, matrix_mulVec] using hab)
    exact congrArg (vectorEquiv n cX) (h.injectiveΓ h')

end
end Decoupling.CoarseCSS
