import Decoupling.HighDim.TorusTensorMapsLift

/-!
# Independence of free models and coherent actual tensor maps

All comparisons are obtained by tensoring genuine lifts of actual
derived isomorphisms. The naturality theorem proves their functor laws.
-/
namespace Decoupling.HighDim.Torus.TensorModel
open CategoryTheory HomologicalComplex
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {D : ℕ} {X Y Z : Derived.{0} K D}

@[simp] theorem map_id (M : TensorModel X) : map M M (𝟙 X) = 𝟙 M.H0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply M.equiv.injective
  rw [equiv_map, Category.comp_id]
  rfl

theorem map_comp (M : TensorModel X) (N : TensorModel Y) (P : TensorModel Z)
    (f : X ⟶ Y) (g : Y ⟶ Z) : map M P (f ≫ g) = map M N f ≫ map N P g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply P.equiv.injective
  change P.equiv (map M P (f ≫ g) x) = P.equiv (map N P g (map M N f x))
  rw [equiv_map, equiv_map, equiv_map, Category.assoc]

@[simp] theorem map_zero (M : TensorModel X) (N : TensorModel Y) : map M N (0 : X ⟶ Y) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply N.equiv.injective
  rw [equiv_map, CategoryTheory.Limits.comp_zero]
  change 0 = N.equiv 0
  exact (N.equiv.map_zero).symm

def isoMap (M : TensorModel X) (N : TensorModel Y) (e : X ≅ Y) : M.H0 ≅ N.H0 where
  hom := map M N e.hom
  inv := map N M e.inv
  hom_inv_id := by rw [← map_comp, e.hom_inv_id, map_id]
  inv_hom_id := by rw [← map_comp, e.inv_hom_id, map_id]

/-- Canonical comparison between any two actual free models of the same
derived object. It is itself induced by actual tensor scalar extension. -/
def comparison (M N : TensorModel X) : M.H0 ≅ N.H0 := isoMap M N (Iso.refl X)

theorem comparison_naturality (M M' : TensorModel X) (N N' : TensorModel Y) (f : X ⟶ Y) :
    (comparison M M').hom ≫ map M' N' f = map M N f ≫ (comparison N N').hom := by
  change map M M' (𝟙 X) ≫ map M' N' f = map M N f ≫ map N N' (𝟙 Y)
  rw [← map_comp, ← map_comp, Category.id_comp, Category.comp_id]

end
end Decoupling.HighDim.Torus.TensorModel
