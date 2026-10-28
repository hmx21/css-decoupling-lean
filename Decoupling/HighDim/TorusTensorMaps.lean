import Decoupling.HighDim.TorusNaturalityTensor

/-!
# Actual scalar-extension maps and bounded free realizations

HD010 Appendix B.3. A derived morphism is lifted to a genuine cochain
map of bounded free models. The torus map is then obtained by actual
extension of scalars and actual homology. Naturality proves independence
of the lift; none of the induced maps is defined by a desired cell formula.
-/
namespace Decoupling.HighDim.Torus
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
variable {K : Type} [Field K] {D : ℕ}

abbrev tensorH0 (C : CochainComplex (ModuleCat (Laurent K D)) ℤ) : ModuleCat K :=
  Layers.coefficients ((((extensionRestricted (augmentation : Laurent K D →+* K)).mapHomologicalComplex
    (.up ℤ)).obj C).homology 0)

/-- The genuine map obtained by tensoring a cochain map and taking H⁰. -/
def tensorH0Map {C E : CochainComplex (ModuleCat (Laurent K D)) ℤ} (f : C ⟶ E) :
    tensorH0 C ⟶ tensorH0 E :=
  (ModuleCat.restrictScalars (constant : K →+* Laurent K D)).map
    (HomologicalComplex.homologyMap
      (((extensionRestricted augmentation).mapHomologicalComplex (.up ℤ)).map f) 0)

def tensorH0Equiv (C : CochainComplex (ModuleCat (Laurent K D)) ℤ)
    [∀ n, Module.Finite (Laurent K D) (C.X n)]
    [∀ n, Module.Free (Laurent K D) (C.X n)] (b : ℤ) [C.IsStrictlyGE b] :
    tensorH0 C ≃ₗ[K] homCoefficients (probe K D) (DerivedCategory.Q.obj C) where
  toFun := tensorNativeEquiv K D C b
  invFun := (tensorNativeEquiv K D C b).symm
  left_inv := (tensorNativeEquiv K D C b).symm_apply_apply
  right_inv := (tensorNativeEquiv K D C b).apply_symm_apply
  map_add' := (tensorNativeEquiv K D C b).map_add
  map_smul' a x := (tensorNativeEquiv K D C b).map_smul (constant a) x

theorem tensorH0Equiv_naturality
    (C E : CochainComplex (ModuleCat (Laurent K D)) ℤ)
    [∀ n, Module.Finite (Laurent K D) (C.X n)] [∀ n, Module.Free (Laurent K D) (C.X n)]
    [∀ n, Module.Finite (Laurent K D) (E.X n)] [∀ n, Module.Free (Laurent K D) (E.X n)]
    (b c : ℤ) [C.IsStrictlyGE b] [E.IsStrictlyGE c] (f : C ⟶ E) (x : tensorH0 C) :
    tensorH0Equiv E c (tensorH0Map f x) =
      (tensorH0Equiv C b x : probe K D ⟶ _) ≫ DerivedCategory.Q.map f :=
  tensorNativeEquiv_naturality K D C E b c f x

/-- A bounded finite-free model with its actual native derived identification.
Existence for the objects used in the final theorems is proved separately. -/
structure TensorModel (X : Derived.{0} K D) where
  complex : CochainComplex (ModuleCat (Laurent K D)) ℤ
  lower : ℤ
  upper : ℤ
  finite : ∀ n, Module.Finite (Laurent K D) (complex.X n)
  free : ∀ n, Module.Free (Laurent K D) (complex.X n)
  boundedBelow : complex.IsStrictlyGE lower
  boundedAbove : complex.IsStrictlyLE upper
  iso : DerivedCategory.Q.obj complex ≅ X

attribute [instance] TensorModel.finite TensorModel.free TensorModel.boundedBelow TensorModel.boundedAbove

namespace TensorModel
variable {X Y Z : Derived.{0} K D}

instance (M : TensorModel X) : M.complex.IsKProjective :=
  CochainComplex.isKProjective_of_projective M.complex M.upper

abbrev H0 (M : TensorModel X) := tensorH0 M.complex

def equiv (M : TensorModel X) : M.H0 ≃ₗ[K] homCoefficients (probe K D) X :=
  (tensorH0Equiv M.complex M.lower).trans (homCoefficientsIso (probe K D) M.iso).toLinearEquiv

theorem exists_lift (M : TensorModel X) (N : TensorModel Y) (f : X ⟶ Y) :
    ∃ g : M.complex ⟶ N.complex, DerivedCategory.Q.map g = M.iso.hom ≫ f ≫ N.iso.inv := by
  obtain ⟨g, hg⟩ := (homotopyQuotient (Laurent K D)).map_surjective
    ((homotopyDerivedEquiv M.complex N.complex).symm (M.iso.hom ≫ f ≫ N.iso.inv))
  refine ⟨g, ?_⟩
  rw [← homotopyDerivedEquiv_map, hg, LinearEquiv.apply_symm_apply]

def lift (M : TensorModel X) (N : TensorModel Y) (f : X ⟶ Y) : M.complex ⟶ N.complex :=
  (exists_lift M N f).choose

theorem lift_spec (M : TensorModel X) (N : TensorModel Y) (f : X ⟶ Y) :
    DerivedCategory.Q.map (lift M N f) = M.iso.hom ≫ f ≫ N.iso.inv :=
  (exists_lift M N f).choose_spec

/-- Tensor the actual chosen lift, then take genuine homology. -/
def map (M : TensorModel X) (N : TensorModel Y) (f : X ⟶ Y) : M.H0 ⟶ N.H0 :=
  tensorH0Map (lift M N f)

theorem equiv_map (M : TensorModel X) (N : TensorModel Y) (f : X ⟶ Y) (x : M.H0) :
    N.equiv (map M N f x) = (M.equiv x : probe K D ⟶ X) ≫ f := by
  change tensorH0Equiv N.complex N.lower (tensorH0Map (lift M N f) x) ≫ N.iso.hom =
    (tensorH0Equiv M.complex M.lower x ≫ M.iso.hom) ≫ f
  have he := tensorH0Equiv_naturality M.complex N.complex M.lower N.lower (lift M N f) x
  change tensorH0Equiv N.complex N.lower (tensorH0Map (lift M N f) x) =
    tensorH0Equiv M.complex M.lower x ≫ DerivedCategory.Q.map (lift M N f) at he
  rw [he, lift_spec]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]


end TensorModel
end
end Decoupling.HighDim.Torus
