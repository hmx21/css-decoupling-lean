import Decoupling.HighDim.SchreyerLocalizationData

/-! # HD014 transporting only the augmented module of an explicit free resolution -/
namespace Decoupling.HighDim.SchreyerLocalization
open CategoryTheory CategoryTheory.Limits
noncomputable section
universe u
variable {R : Type u} [CommRing R] {M N : ModuleCat.{u} R} {length : ℕ}
set_option backward.isDefEq.respectTransparency false

def FreeData.transport (A : FreeData M length) (e : M ≅ N) : FreeData N length where
  data := {
    A.data with
    ε := A.data.ε ≫ e.hom
    d_ε := by rw [←Category.assoc,A.data.d_ε,zero_comp]
    surjective := e.toLinearEquiv.surjective.comp A.data.surjective
    exact_zero := by
      rw [A.data.exact_zero]
      ext x
      change A.data.ε x=0 ↔ e.hom (A.data.ε x)=0
      exact (e.toLinearEquiv.map_eq_zero_iff).symm }
  rank := A.rank
  coordinates := A.coordinates

@[simp] theorem FreeData.transport_X (A : FreeData M length) (e : M ≅ N) (k : ℕ) :
    (A.transport e).data.X k = A.data.X k := rfl

@[simp] theorem FreeData.transport_augmentation (A : FreeData M length) (e : M ≅ N) :
    (A.transport e).data.ε = A.data.ε ≫ e.hom := rfl

end
end Decoupling.HighDim.SchreyerLocalization
