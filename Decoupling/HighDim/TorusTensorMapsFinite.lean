import Decoupling.HighDim.TorusTensorMapsCycles
import Decoupling.HighDim.TorusTensorLocalDuality
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finiteness of actual torus homology of bounded finite-free models

This is proved directly from scalar extension and the actual cycle
quotient; no finiteness of a represented Hom space is an input.
-/
namespace Decoupling.HighDim.Torus
open CategoryTheory HomologicalComplex TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] {D : ℕ}

instance augmentationExtension_finite (M : ModuleCat (Laurent K D))
    [Module.Finite (Laurent K D) M] :
    Module.Finite K ((ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).obj M) := by
  let : Algebra (Laurent K D) K := (augmentation : Laurent K D →+* K).toAlgebra
  change Module.Finite K (K ⊗[Laurent K D] M)
  infer_instance

instance tensorH0_finite (C : CochainComplex (ModuleCat (Laurent K D)) ℤ)
    [Module.Finite (Laurent K D) (C.X 0)] : Module.Finite K (tensorH0 C) := by
  let S := (tensorRestrictedComplex C).sc 0
  let F := ModuleCat.restrictScalars (constant : K →+* Laurent K D)
  have he : F.obj S.X₂ ≅ (ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).obj (C.X 0) :=
    (augmentationCoefficientsIso K D).app _
  let : Module.Finite K (S.map F).X₂ := Module.Finite.equiv he.symm.toLinearEquiv
  let : Module.Finite K (S.map F).homology := finite_homology (S.map F)
  exact Module.Finite.equiv (S.mapHomologyIso F).toLinearEquiv

instance TensorModel.finiteH0 {X : Derived.{0} K D} (M : TensorModel X) : Module.Finite K M.H0 :=
  tensorH0_finite M.complex

end
end Decoupling.HighDim.Torus
