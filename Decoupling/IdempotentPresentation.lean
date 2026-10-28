import Mathlib.RingTheory.Finiteness.Projective
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Finite projectives and idempotent matrices

These are preparatory algebraic reductions for the outstanding Laurent
projective-freeness theorem. They use native `Module.Projective` and
`Module.Free`. No theorem asserting that Laurent projectives are free is
assumed here. Matrices follow this project's column-vector convention.
-/

namespace Decoupling.IdempotentPresentation

open Matrix Module

noncomputable section

variable {A P : Type*} [CommRing A] [AddCommGroup P] [Module A P]

structure SplitCover (P : Type*) [AddCommGroup P] [Module A P] (n : ℕ) where
  π : (Fin n → A) →ₗ[A] P
  ι : P →ₗ[A] (Fin n → A)
  retract : π.comp ι = LinearMap.id

theorem exists_splitCover [Module.Finite A P] [Module.Projective A P] :
    ∃ n : ℕ, Nonempty (SplitCover (A := A) P n) := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' A P
  obtain ⟨ι, hι⟩ := Module.projective_lifting_property π LinearMap.id hπ
  exact ⟨n, ⟨⟨π, ι, hι⟩⟩⟩

namespace SplitCover

variable {n : ℕ} (c : SplitCover (A := A) P n)

def projector : (Fin n → A) →ₗ[A] (Fin n → A) := c.ι.comp c.π

@[simp] theorem π_ι (p : P) : c.π (c.ι p) = p := DFunLike.congr_fun c.retract p

theorem projector_idempotent : c.projector.comp c.projector = c.projector := by
  ext v
  simp [projector]

def toRange : P →ₗ[A] LinearMap.range c.projector :=
  c.ι.codRestrict _ (by
    intro p
    exact ⟨c.ι p, by simp [projector]⟩)

def rangeEquiv : P ≃ₗ[A] LinearMap.range c.projector where
  toLinearMap := c.toRange
  invFun v := c.π v
  left_inv p := c.π_ι p
  right_inv v := by
    apply Subtype.ext
    obtain ⟨w, hw⟩ := v.property
    change c.projector (v : Fin n → A) = (v : Fin n → A)
    rw [← hw]
    exact DFunLike.congr_fun c.projector_idempotent w

def matrix : Matrix (Fin n) (Fin n) A := LinearMap.toMatrix' c.projector

theorem matrix_linearMap : c.matrix.mulVecLin = c.projector := by
  apply LinearMap.ext
  intro v
  funext i
  exact congrFun (LinearMap.toMatrix'_mulVec c.projector v) i

theorem matrix_idempotent : c.matrix * c.matrix = c.matrix := by
  apply Matrix.mulVec_injective
  funext v
  rw [← Matrix.mulVec_mulVec]
  change c.matrix.mulVecLin (c.matrix.mulVecLin v) = c.matrix.mulVecLin v
  rw [c.matrix_linearMap]
  exact DFunLike.congr_fun c.projector_idempotent v

end SplitCover

/-- Every genuine finite projective module is the image of an idempotent matrix. -/
theorem exists_idempotent [Module.Finite A P] [Module.Projective A P] :
    ∃ n : ℕ, ∃ E : Matrix (Fin n) (Fin n) A,
      E * E = E ∧ Nonempty (P ≃ₗ[A] LinearMap.range E.mulVecLin) := by
  obtain ⟨n, ⟨c⟩⟩ := exists_splitCover (A := A) (P := P)
  refine ⟨n, c.matrix, c.matrix_idempotent, ⟨?_⟩⟩
  rw [c.matrix_linearMap]
  exact c.rangeEquiv

section Factorization

variable {n k : ℕ} (E : Matrix (Fin n) (Fin n) A) (hE : E * E = E)
  (F : Matrix (Fin n) (Fin k) A) (G : Matrix (Fin k) (Fin n) A)
  (hFG : F * G = E) (hGF : G * F = 1)

/-- Rectangular inverse factors give an actual basis of the image, not just a
rank count or a proposition relabeled as freeness. -/
def factorEquiv : (Fin k → A) ≃ₗ[A] LinearMap.range E.mulVecLin where
  toLinearMap := F.mulVecLin.codRestrict _ (by
    intro v
    refine ⟨F *ᵥ v, ?_⟩
    change E *ᵥ (F *ᵥ v) = F *ᵥ v
    rw [Matrix.mulVec_mulVec, ← hFG, Matrix.mul_assoc, hGF, Matrix.mul_one])
  invFun v := G *ᵥ (v : Fin n → A)
  left_inv v := by
    change G *ᵥ (F *ᵥ v) = v
    rw [Matrix.mulVec_mulVec, hGF, Matrix.one_mulVec]
  right_inv v := by
    apply Subtype.ext
    change F *ᵥ (G *ᵥ (v : Fin n → A)) = (v : Fin n → A)
    rw [Matrix.mulVec_mulVec, hFG]
    obtain ⟨w, hw⟩ := v.property
    change E *ᵥ (v : Fin n → A) = (v : Fin n → A)
    rw [← hw]
    change E *ᵥ (E *ᵥ w) = E *ᵥ w
    rw [Matrix.mulVec_mulVec, hE]

include hE hFG hGF in
theorem free_of_factorization : Module.Free A (LinearMap.range E.mulVecLin) :=
  Module.Free.of_equiv (factorEquiv E hE F G hFG hGF)

end Factorization

section Converse

variable {n k : ℕ} (E : Matrix (Fin n) (Fin n) A) (hE : E * E = E)

include hE

theorem fixes_range (v : LinearMap.range E.mulVecLin) : E *ᵥ (v : Fin n → A) = v := by
  obtain ⟨w, hw⟩ := v.property
  rw [← hw]
  change E *ᵥ (E *ᵥ w) = E *ᵥ w
  rw [Matrix.mulVec_mulVec, hE]

/-- The image of an actual idempotent is a projective direct summand. -/
theorem projective_range : Module.Projective A (LinearMap.range E.mulVecLin) := by
  apply Module.Projective.of_split (LinearMap.range E.mulVecLin).subtype
    E.mulVecLin.rangeRestrict
  apply LinearMap.ext
  intro v
  exact Subtype.ext (fixes_range E hE v)

/-- A free basis of an idempotent image supplies rectangular inverse factors. -/
theorem factors_of_equiv (e : (Fin k → A) ≃ₗ[A] LinearMap.range E.mulVecLin) :
    ∃ F : Matrix (Fin n) (Fin k) A, ∃ G : Matrix (Fin k) (Fin n) A,
      F * G = E ∧ G * F = 1 := by
  let f := (LinearMap.range E.mulVecLin).subtype.comp e.toLinearMap
  let g := e.symm.toLinearMap.comp E.mulVecLin.rangeRestrict
  let F := LinearMap.toMatrix' f
  let G := LinearMap.toMatrix' g
  have hf (v : Fin k → A) : F *ᵥ v = (e v : Fin n → A) :=
    LinearMap.toMatrix'_mulVec f v
  have hg (v : Fin n → A) : G *ᵥ v = e.symm (E.mulVecLin.rangeRestrict v) :=
    LinearMap.toMatrix'_mulVec g v
  refine ⟨F, G, ?_, ?_⟩
  · apply Matrix.mulVec_injective
    funext v
    rw [← Matrix.mulVec_mulVec, hf, hg, e.apply_symm_apply]
    rfl
  · apply Matrix.mulVec_injective
    funext v
    rw [← Matrix.mulVec_mulVec, hg, hf, Matrix.one_mulVec]
    have hv : E.mulVecLin.rangeRestrict (e v) = e v :=
      Subtype.ext (fixes_range E hE (e v))
    rw [hv, e.symm_apply_apply]

theorem free_iff_factorization [Nontrivial A] :
    Module.Free A (LinearMap.range E.mulVecLin) ↔
      ∃ k : ℕ, ∃ F : Matrix (Fin n) (Fin k) A, ∃ G : Matrix (Fin k) (Fin n) A,
        F * G = E ∧ G * F = 1 := by
  constructor
  · intro h
    let := h
    let b := Module.finBasis A (LinearMap.range E.mulVecLin)
    exact ⟨_, factors_of_equiv E hE b.equivFun.symm⟩
  · rintro ⟨k, F, G, hFG, hGF⟩
    exact free_of_factorization E hE F G hFG hGF

end Converse

/-- The rectangular factor relation, in column-vector orientation. -/
def Related {n m : ℕ} (E : Matrix (Fin n) (Fin n) A) (F : Matrix (Fin m) (Fin m) A) : Prop :=
  ∃ a : Matrix (Fin n) (Fin m) A, ∃ b : Matrix (Fin m) (Fin n) A,
    a * b = E ∧ b * a = F

namespace Related

variable {n m k : ℕ} {E : Matrix (Fin n) (Fin n) A}
  {F : Matrix (Fin m) (Fin m) A} {G : Matrix (Fin k) (Fin k) A}

theorem refl (hE : E * E = E) : Related E E := ⟨E, E, hE, hE⟩

theorem symm (h : Related E F) : Related F E := by
  obtain ⟨a, b, hab, hba⟩ := h
  exact ⟨b, a, hba, hab⟩

theorem trans (hEF : Related E F) (hFG : Related F G)
    (hE : E * E = E) (hG : G * G = G) : Related E G := by
  obtain ⟨a, b, hab, hba⟩ := hEF
  obtain ⟨c, d, hcd, hdc⟩ := hFG
  refine ⟨a * c, d * b, ?_, ?_⟩
  · calc
      (a * c) * (d * b) = a * (c * d) * b := by simp only [Matrix.mul_assoc]
      _ = a * (b * a) * b := by rw [hcd, ← hba]
      _ = (a * b) * (a * b) := by simp only [Matrix.mul_assoc]
      _ = E := by rw [hab, hE]
  · calc
      (d * b) * (a * c) = d * (b * a) * c := by simp only [Matrix.mul_assoc]
      _ = d * (c * d) * c := by rw [hba, ← hcd]
      _ = (d * c) * (d * c) := by simp only [Matrix.mul_assoc]
      _ = G := by rw [hdc, hG]

theorem map {B : Type*} [CommRing B] (f : A →+* B) (h : Related E F) :
    Related (E.map f) (F.map f) := by
  obtain ⟨a, b, hab, hba⟩ := h
  exact ⟨a.map f, b.map f, by rw [← Matrix.map_mul, hab],
    by rw [← Matrix.map_mul, hba]⟩

end Related
end
end Decoupling.IdempotentPresentation
