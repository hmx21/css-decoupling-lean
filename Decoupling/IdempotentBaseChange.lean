import Decoupling.ProjectiveFreeness
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.RingTheory.Localization.BaseChange

/-!
# Scalar extension of an actual idempotent image

The tensor product of the original projective image is identified with the
image of the coefficient-mapped matrix, over any commutative algebra.
-/

namespace Decoupling.IdempotentBaseChange

open TensorProduct IdempotentPresentation
open scoped TensorProduct

noncomputable section

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {n : ℕ} (E : Matrix (Fin n) (Fin n) A) (hE : E * E = E)

abbrev Image := LinearMap.range E.mulVecLin

def coordinates : (B ⊗[A] (Fin n → A)) ≃ₗ[B] (Fin n → B) :=
  TensorProduct.piScalarRight A B B (Fin n)

theorem coordinates_matrix (x : B ⊗[A] (Fin n → A)) :
    coordinates (E.mulVecLin.baseChange B x) =
      (E.map (algebraMap A B)).mulVecLin (coordinates x) := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy => simp [map_add, hx, hy]
  | tmul b v =>
    funext i
    simp only [LinearMap.baseChange_tmul, coordinates, TensorProduct.piScalarRight_apply,
      TensorProduct.piScalarRightHom_tmul, Matrix.mulVecLin_apply, Matrix.mulVec,
      dotProduct, Algebra.smul_def, map_sum, map_mul, Finset.sum_mul, Matrix.map_apply]
    apply Finset.sum_congr rfl
    intro j _
    ring

def inclusion : (B ⊗[A] Image E) →ₗ[B] (Fin n → B) :=
  coordinates.toLinearMap.comp ((LinearMap.range E.mulVecLin).subtype.baseChange B)

def projection : (Fin n → B) →ₗ[B] (B ⊗[A] Image E) :=
  (E.mulVecLin.rangeRestrict.baseChange B).comp coordinates.symm.toLinearMap

include hE in
theorem projection_inclusion (x : B ⊗[A] Image E) : projection E (inclusion E x) = x := by
  have h : E.mulVecLin.rangeRestrict.comp (LinearMap.range E.mulVecLin).subtype = LinearMap.id := by
    apply LinearMap.ext
    intro v
    exact Subtype.ext (fixes_range E hE v)
  have hh := congrArg (fun f => f.baseChange B) h
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_id] at hh
  dsimp only [projection, inclusion, LinearMap.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.symm_apply_apply]
  exact DFunLike.congr_fun hh x

theorem inclusion_projection (v : Fin n → B) : inclusion E (projection E v) =
    (E.map (algebraMap A B)).mulVecLin v := by
  have h : (LinearMap.range E.mulVecLin).subtype.comp E.mulVecLin.rangeRestrict = E.mulVecLin := rfl
  have hh := congrArg (fun f => f.baseChange B) h
  rw [LinearMap.baseChange_comp] at hh
  dsimp only [projection, inclusion, LinearMap.comp_apply, LinearEquiv.coe_coe]
  change coordinates (((LinearMap.range E.mulVecLin).subtype.baseChange B).comp
    (E.mulVecLin.rangeRestrict.baseChange B) (coordinates.symm v)) = _
  rw [hh, coordinates_matrix, LinearEquiv.apply_symm_apply]

/-- Exact scalar-extension identification, requiring no flatness input. -/
def imageEquiv : (B ⊗[A] Image E) ≃ₗ[B]
    LinearMap.range (E.map (algebraMap A B)).mulVecLin where
  toLinearMap := (inclusion E).codRestrict _ (by
    intro x
    refine ⟨inclusion E x, ?_⟩
    rw [← inclusion_projection, projection_inclusion E hE])
  invFun v := projection E v
  left_inv x := projection_inclusion E hE x
  right_inv v := by
    apply Subtype.ext
    change inclusion E (projection E (v : Fin n → B)) = (v : Fin n → B)
    rw [inclusion_projection]
    exact fixes_range (E.map (algebraMap A B)) (by rw [← Matrix.map_mul, hE]) v

/-- For an actual module localization, the tensor identification gives the
corresponding localized idempotent image over the localized coefficient ring. -/
def localizedImageEquiv (S : Submonoid A) [IsLocalization S B]
    {P : Type*} [AddCommGroup P] [Module A P] [Module B P] [IsScalarTower A B P]
    (f : Image E →ₗ[A] P) [IsLocalizedModule S f] :
    P ≃ₗ[B] LinearMap.range (E.map (algebraMap A B)).mulVecLin :=
  (IsLocalizedModule.isBaseChange S B f).equiv.symm.trans (imageEquiv E hE)

include hE in
theorem free_localized_of_free_image (S : Submonoid A) [IsLocalization S B]
    {P : Type*} [AddCommGroup P] [Module A P] [Module B P] [IsScalarTower A B P]
    (f : Image E →ₗ[A] P) [IsLocalizedModule S f]
    (hf : Module.Free B (LinearMap.range (E.map (algebraMap A B)).mulVecLin)) :
    Module.Free B P := by
  let := hf
  exact Module.Free.of_equiv (localizedImageEquiv E hE S f).symm

end
end Decoupling.IdempotentBaseChange
