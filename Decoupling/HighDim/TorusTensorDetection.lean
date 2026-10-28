import Decoupling.HighDim.TorusExactLoss
import Decoupling.HighDim.TorusYonedaDetection

/-!
# Genuine nonzero attachments give nonzero tensor maps and strict loss

HD010 Appendix B.3. Detection is proved from native Koszul Yoneda
composition and actual tensor naturality. It is not an assumed
faithfulness property of tensoring or of an arbitrary representable functor.
-/
namespace Decoupling.HighDim.Torus
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ}

/-- Within the manuscript's layer degree range, zero of the actual
tensor-induced connecting-component map is exactly zero of that component. -/
theorem tensor_connecting_zero_iff
    (B A : ModuleCat (Laurent K D)) [Module.Finite K (Layers.coefficients B)]
    (hB : TrivialLayers.AugmentationAction B) (hA : TrivialLayers.AugmentationAction A)
    (i j : ℤ) (hi : 1 ≤ i) (hij : i < j) (hj : j < D)
    (M : TensorModel ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj B))
    (N : TensorModel (((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj A)⟦(1 : ℤ)⟧))
    (δ : (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj B ⟶
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj A)⟦(1 : ℤ)⟧) :
    TensorModel.map M N δ = 0 ↔ δ = 0 := by
  constructor
  · intro h
    apply probe_detects_connecting B A hB hA i j hi hij hj δ
    intro g
    have he := TensorModel.equiv_map M N δ (M.equiv.symm g)
    rw [h, LinearEquiv.apply_symm_apply] at he
    change N.equiv 0 = g ≫ δ at he
    rw [LinearEquiv.map_zero] at he
    exact he.symm
  · rintro rfl
    exact TensorModel.map_zero M N

/-- Both rank losses are actual linear-map losses. A nonzero outgoing
tensor connecting map alone forces strict inequality. -/
theorem tensor_triangle_strict_of_connecting
    (T : Triangle (Derived.{0} K D)) (hT : T ∈ distTriang _)
    (M : TensorModel T.obj₁) (N : TensorModel T.obj₂) (P : TensorModel T.obj₃)
    (Q : TensorModel (T.obj₁⟦(1 : ℤ)⟧))
    (hδ : TensorModel.map P Q T.mor₃ ≠ 0) :
    Module.finrank K N.H0 < Module.finrank K M.H0 + Module.finrank K P.H0 := by
  have hr : Module.finrank K (TensorModel.map P Q T.mor₃).hom.range ≠ 0 := by
    intro hz
    exact hδ (ModuleCat.hom_ext (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hz)))
  have he := tensor_triangle_dimension T hT M N P Q
  omega

end
end Decoupling.HighDim.Torus
