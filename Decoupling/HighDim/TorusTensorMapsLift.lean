import Decoupling.HighDim.TorusTensorMaps
namespace Decoupling.HighDim.Torus.TensorModel
open CategoryTheory HomologicalComplex
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
variable {K : Type} [Field K] {D : ℕ} {X Y : Derived.{0} K D}
attribute [local irreducible] lift tensorH0Equiv

theorem map_eq_of_lift (M : TensorModel X) (N : TensorModel Y) (f : X ⟶ Y)
    (g : M.complex ⟶ N.complex) (hg : DerivedCategory.Q.map g = M.iso.hom ≫ f ≫ N.iso.inv) :
    map M N f = tensorH0Map g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply (tensorH0Equiv N.complex N.lower).injective
  change tensorH0Equiv N.complex N.lower (tensorH0Map (lift M N f) x) =
    tensorH0Equiv N.complex N.lower (tensorH0Map g x)
  exact (tensorH0Equiv_naturality M.complex N.complex M.lower N.lower (lift M N f) x).trans
    ((congrArg (fun u => (tensorH0Equiv M.complex M.lower x : probe K D ⟶ _) ≫ u)
      ((lift_spec M N f).trans hg.symm)).trans
      (tensorH0Equiv_naturality M.complex N.complex M.lower N.lower g x).symm)

end
end Decoupling.HighDim.Torus.TensorModel
