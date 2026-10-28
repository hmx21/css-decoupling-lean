import Decoupling.HighDim.TorusTensorMapsFinite

/-!
# Linear maps from genuine cycles to actual tensor homology

When the actual outgoing tensor differential is proved zero, every term
element defines a genuine class. Linearity is inherited from the native
homology projection, and naturality from the actual homology map.
-/
namespace Decoupling.HighDim.Torus
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]

def zeroDifferentialClass (S : ShortComplex (ModuleCat R)) (hg : S.g = 0) : S.X₂ ⟶ S.homology :=
  ModuleCat.ofHom {
    toFun x := (⟨x, by rw [hg]; rfl⟩ : LinearMap.ker S.g.hom)
    map_add' _ _ := rfl
    map_smul' _ _ := rfl } ≫ S.moduleCatCyclesIso.inv ≫ S.homologyπ

@[simp] theorem zeroDifferentialClass_apply (S : ShortComplex (ModuleCat R)) (hg : S.g = 0)
    (x : S.X₂) : zeroDifferentialClass S hg x = Glued.cycleClass S x (by rw [hg]; rfl) := rfl

theorem zeroDifferentialClass_naturality {S T : ShortComplex (ModuleCat R)}
    (f : S ⟶ T) (hS : S.g = 0) (hT : T.g = 0) :
    zeroDifferentialClass S hS ≫ ShortComplex.homologyMap f = f.τ₂ ≫ zeroDifferentialClass T hT := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ShortComplex.homologyMap f (Glued.cycleClass S x _) = Glued.cycleClass T (f.τ₂ x) _
  exact Glued.homologyMap_cycleClass f x _

theorem zeroDifferentialClass_bijective (S : ShortComplex (ModuleCat R))
    (hf : S.f = 0) (hg : S.g = 0) : Function.Bijective (zeroDifferentialClass S hg) := by
  constructor
  · intro x y hxy
    have hz : Glued.cycleClass S (x - y) (by rw [hg]; rfl) = 0 := by
      change zeroDifferentialClass S hg (x - y) = 0
      rw [map_sub, hxy, sub_self]
    obtain ⟨z, hz⟩ := (Glued.cycleClass_eq_zero_iff S _ _).mp hz
    rw [hf] at hz
    exact sub_eq_zero.mp (by simpa using hz.symm)
  · intro z
    obtain ⟨x, hx, rfl⟩ := Glued.cycleClass_surjective S z
    exact ⟨x, rfl⟩

variable {K : Type} [Field K] {D : ℕ}

def tensorClasses (C : CochainComplex (ModuleCat (Laurent K D)) ℤ)
    (h : (tensorRestrictedComplex C).d 0 ((ComplexShape.up ℤ).next 0) = 0) :
    Layers.coefficients ((tensorRestrictedComplex C).X 0) ⟶ tensorH0 C :=
  (ModuleCat.restrictScalars (constant : K →+* Laurent K D)).map
    (zeroDifferentialClass ((tensorRestrictedComplex C).sc 0) h)

theorem tensorClasses_naturality {C E : CochainComplex (ModuleCat (Laurent K D)) ℤ}
    (f : C ⟶ E)
    (hC : (tensorRestrictedComplex C).d 0 ((ComplexShape.up ℤ).next 0) = 0)
    (hE : (tensorRestrictedComplex E).d 0 ((ComplexShape.up ℤ).next 0) = 0) :
    tensorClasses C hC ≫ tensorH0Map f =
      (ModuleCat.restrictScalars (constant : K →+* Laurent K D)).map
        ((extensionRestricted augmentation).map (f.f 0)) ≫ tensorClasses E hE := by
  exact congrArg ((ModuleCat.restrictScalars (constant : K →+* Laurent K D)).map)
    (zeroDifferentialClass_naturality
      ((shortComplexFunctor (ModuleCat (Laurent K D)) (.up ℤ) 0).map
        (((extensionRestricted augmentation).mapHomologicalComplex (.up ℤ)).map f)) hC hE)

/-- The cycle projection with the actual scalar-extended K-module as
source, using the proved identity-on-elements coefficient identification. -/
def tensorClassesFromField (C : CochainComplex (ModuleCat (Laurent K D)) ℤ)
    (h : (tensorRestrictedComplex C).d 0 ((ComplexShape.up ℤ).next 0) = 0) :
    (ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).obj (C.X 0) ⟶ tensorH0 C :=
  ((augmentationCoefficientsIso K D).app _).inv ≫ tensorClasses C h

theorem tensorClassesFromField_naturality
    {C E : CochainComplex (ModuleCat (Laurent K D)) ℤ} (f : C ⟶ E)
    (hC : (tensorRestrictedComplex C).d 0 ((ComplexShape.up ℤ).next 0) = 0)
    (hE : (tensorRestrictedComplex E).d 0 ((ComplexShape.up ℤ).next 0) = 0) :
    tensorClassesFromField C hC ≫ tensorH0Map f =
      (ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).map (f.f 0) ≫
        tensorClassesFromField E hE := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change ShortComplex.homologyMap
    ((shortComplexFunctor (ModuleCat (Laurent K D)) (.up ℤ) 0).map
      (((extensionRestricted augmentation).mapHomologicalComplex (.up ℤ)).map f))
    (Glued.cycleClass ((tensorRestrictedComplex C).sc 0) x _) =
      Glued.cycleClass ((tensorRestrictedComplex E).sc 0)
        ((ModuleCat.extendScalars augmentation).map (f.f 0) x) _
  exact Glued.homologyMap_cycleClass
    ((shortComplexFunctor (ModuleCat (Laurent K D)) (.up ℤ) 0).map
      (((extensionRestricted augmentation).mapHomologicalComplex (.up ℤ)).map f))
    (show (tensorRestrictedComplex C).X 0 from x) _

/-- With both actual differentials zero, the actual homology is exactly
its degree-zero tensor term; this proves the cell coordinates are a
true homology basis, rather than only names for classes. -/
def tensorClassesFromFieldIso (C : CochainComplex (ModuleCat (Laurent K D)) ℤ)
    (hf : (tensorRestrictedComplex C).d ((ComplexShape.up ℤ).prev 0) 0 = 0)
    (hg : (tensorRestrictedComplex C).d 0 ((ComplexShape.up ℤ).next 0) = 0) :
    (ModuleCat.extendScalars (augmentation : Laurent K D →+* K)).obj (C.X 0) ≅ tensorH0 C := by
  let f := tensorClassesFromField C hg
  have hi : Function.Bijective f := zeroDifferentialClass_bijective
    ((tensorRestrictedComplex C).sc 0) hf hg
  let := (ConcreteCategory.isIso_iff_bijective f).mpr hi
  exact asIso f

@[simp] theorem tensorClassesFromFieldIso_hom (C : CochainComplex (ModuleCat (Laurent K D)) ℤ)
    (hf : (tensorRestrictedComplex C).d ((ComplexShape.up ℤ).prev 0) 0 = 0)
    (hg : (tensorRestrictedComplex C).d 0 ((ComplexShape.up ℤ).next 0) = 0) :
    (tensorClassesFromFieldIso C hf hg).hom = tensorClassesFromField C hg := rfl

end
end Decoupling.HighDim.Torus
