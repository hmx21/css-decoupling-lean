import Decoupling.HighDim.TorusTensorMapsFinite
import Decoupling.HighDim.AdjacentGluing

/-!
# Exact loss for genuine tensor-induced adjacent-triangle maps

HD010 Appendix B.3, equation B1. This module first proves the invariant
formula for any actual bounded free realizations. Model existence and
the finite-layer final specialization are supplied by the paper interfaces.
-/
namespace Decoupling.HighDim.Torus
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open PostnikovInduction
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] {D : ℕ}

namespace TensorModel
variable {X Y Z : Derived.{0} K D}

theorem map_exact (M : TensorModel X) (N : TensorModel Y) (P : TensorModel Z)
    (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : Function.Exact (postcompose (probe K D) f) (postcompose (probe K D) g)) :
    Function.Exact (map M N f) (map N P g) := by
  intro y
  constructor
  · intro hy
    have hz : postcompose (probe K D) g (N.equiv y) = 0 := by
      change (N.equiv y : probe K D ⟶ Y) ≫ g = 0
      rw [← equiv_map, hy]
      exact P.equiv.map_zero
    obtain ⟨x, hx⟩ := (h (N.equiv y)).mp hz
    refine ⟨M.equiv.symm x, N.equiv.injective ?_⟩
    rw [equiv_map, LinearEquiv.apply_symm_apply]
    exact hx
  · rintro ⟨x, rfl⟩
    apply P.equiv.injective
    rw [equiv_map, equiv_map]
    erw [LinearEquiv.map_zero]
    exact (h (postcompose (probe K D) f (M.equiv x))).mpr ⟨M.equiv x, rfl⟩

end TensorModel

theorem tensor_triangle_exact (T : Triangle (Derived.{0} K D)) (hT : T ∈ distTriang _)
    (M : TensorModel T.obj₁) (N : TensorModel T.obj₂) (P : TensorModel T.obj₃) :
    Function.Exact (TensorModel.map M N T.mor₁) (TensorModel.map N P T.mor₂) :=
  TensorModel.map_exact M N P _ _ (postcompose_exact (probe K D) T hT)

theorem tensor_triangle_connecting_exact (T : Triangle (Derived.{0} K D)) (hT : T ∈ distTriang _)
    (N : TensorModel T.obj₂) (P : TensorModel T.obj₃) (Q : TensorModel (T.obj₁⟦(1 : ℤ)⟧)) :
    Function.Exact (TensorModel.map N P T.mor₂) (TensorModel.map P Q T.mor₃) :=
  TensorModel.map_exact N P Q _ _ (postcompose_connecting_exact (probe K D) T hT)

theorem tensor_triangle_finite_middle (T : Triangle (Derived.{0} K D)) (hT : T ∈ distTriang _)
    (M : TensorModel T.obj₁) (N : TensorModel T.obj₂) (P : TensorModel T.obj₃)
    : Module.Finite K N.H0 := by
  let : Module.Finite K (homCoefficients (probe K D) T.obj₁) := Module.Finite.equiv M.equiv
  let : Module.Finite K (homCoefficients (probe K D) T.obj₃) := Module.Finite.equiv P.equiv
  let := homCoefficients_finite_middle (probe K D) T hT
  exact Module.Finite.equiv N.equiv.symm

/-- Both losses, for actual tensor-induced maps. The kernel term is the
kernel of the actual inclusion-induced map, not a proxy for it. -/
theorem tensor_triangle_dimension (T : Triangle (Derived.{0} K D)) (hT : T ∈ distTriang _)
    (M : TensorModel T.obj₁) (N : TensorModel T.obj₂) (P : TensorModel T.obj₃)
    (Q : TensorModel (T.obj₁⟦(1 : ℤ)⟧)) :
    Module.finrank K N.H0 + Module.finrank K (TensorModel.map M N T.mor₁).hom.ker +
      Module.finrank K (TensorModel.map P Q T.mor₃).hom.range =
        Module.finrank K M.H0 + Module.finrank K P.H0 := by
  let := tensor_triangle_finite_middle T hT M N P
  have hm := finrank_of_exact _ _ (tensor_triangle_exact T hT M N P)
  have hp := finrank_of_exact _ _ (tensor_triangle_connecting_exact T hT N P Q)
  have hk := (TensorModel.map M N T.mor₁).hom.finrank_range_add_finrank_ker
  omega

/-- The adjacent triangle with its genuine homology module as third
object; its arrows include the proved endpoint isomorphism. -/
def adjacentTriangle (X : Derived.{0} K D) (j : ℤ) : Triangle (Derived.{0} K D) :=
  Triangle.mk (AdjacentGluing.rawTriangle X j).mor₁
    ((AdjacentGluing.rawTriangle X j).mor₂ ≫ (AdjacentGluing.layerIso X j).hom)
    (AdjacentGluing.delta X j)

def adjacentTriangleIso (X : Derived.{0} K D) (j : ℤ) :
    AdjacentGluing.rawTriangle X j ≅ adjacentTriangle X j := by
  refine Triangle.isoMk _ _ (Iso.refl _) (Iso.refl _) (AdjacentGluing.layerIso X j)
    (by simp [adjacentTriangle]) (by simp [adjacentTriangle]) ?_
  simp [adjacentTriangle, AdjacentGluing.delta]

theorem adjacentTriangle_distinguished (X : Derived.{0} K D) (j : ℤ) :
    adjacentTriangle X j ∈ distTriang _ :=
  isomorphic_distinguished _ (AdjacentGluing.rawTriangle_distinguished X j) _
    (adjacentTriangleIso X j).symm

/-- B1, before choosing models: valid for every bounded finite-free
model of the actual four objects and their actual derived arrows. -/
theorem adjacent_tensor_dimension (X : Derived.{0} K D) (j : ℤ)
    (M : TensorModel (PostnikovTruncation.lower X j))
    (N : TensorModel (AdjacentGluing.cap X j))
    (P : TensorModel ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj (H X j)))
    (Q : TensorModel ((PostnikovTruncation.lower X j)⟦(1 : ℤ)⟧))
    :
    Module.finrank K N.H0 +
      Module.finrank K (TensorModel.map M N (AdjacentGluing.rawTriangle X j).mor₁).hom.ker +
      Module.finrank K (TensorModel.map P Q (AdjacentGluing.delta X j)).hom.range =
        Module.finrank K M.H0 + Module.finrank K P.H0 :=
  tensor_triangle_dimension (adjacentTriangle X j) (adjacentTriangle_distinguished X j) M N P Q

end
end Decoupling.HighDim.Torus
