import Decoupling.HighDim.TorusPeriodic
import Decoupling.HighDim.FiniteResolutionProfile
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Scalar extension of the actual finite free CSS window

Source: Appendix B.3. This constructs actual tensor-product coordinates
for free modules and proves their compatibility with entrywise matrix
base change. It is the concrete bridge from the periodic checks to the
base-changed finite free cochain model.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits TensorProduct Matrix
open scoped ChangeOfRings
noncomputable section
set_option backward.isDefEq.respectTransparency false

section General
variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

/-- Free-module coordinates for genuine extension of scalars. -/
def extensionFreeIso (n : ℕ) :
    (ModuleCat.extendScalars φ).obj (ModuleCat.of R (Fin n → R)) ≅
      ModuleCat.of S (Fin n → S) := by
  letI : Algebra R S := φ.toAlgebra
  exact (TensorProduct.piScalarRight R S S (Fin n)).toModuleIso

@[simp] theorem extensionFreeIso_tmul (n : ℕ) (a : S) (v : Fin n → R) :
    (extensionFreeIso φ n).hom ((a ⊗ₜ[R,φ] v)) =
      fun i => φ (v i) * a := by
  let : Algebra R S := φ.toAlgebra
  change TensorProduct.piScalarRight R S S (Fin n) (a ⊗ₜ[R] v) = _
  rw [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul]
  rfl

/-- Scalar extension of a matrix map is its entrywise mapped matrix. -/
theorem extensionFreeIso_naturality {m n : ℕ} (M : Matrix (Fin m) (Fin n) R) :
    (ModuleCat.extendScalars φ).map (ModuleCat.ofHom M.mulVecLin) ≫
      (extensionFreeIso φ m).hom =
        (extensionFreeIso φ n).hom ≫ ModuleCat.ofHom (M.map φ).mulVecLin := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro v
  change (extensionFreeIso φ m).hom
      ((ModuleCat.extendScalars φ).map (ModuleCat.ofHom M.mulVecLin)
        ((1 : S) ⊗ₜ[R,φ] v)) =
    ((M.map φ).mulVecLin) ((extensionFreeIso φ n).hom ((1 : S) ⊗ₜ[R,φ] v))
  rw [ModuleCat.ExtendScalars.map_tmul, extensionFreeIso_tmul, extensionFreeIso_tmul]
  funext i
  simp [Matrix.mulVec, dotProduct, map_sum]

end General
end
end Decoupling.HighDim.Torus
