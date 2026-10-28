import Decoupling.HighDim.TorusLocalDuality

/-!
# Naturality of genuine localization and cochain duality

HD010, Appendix B.3. All maps are actual cochain maps or their actual
homotopy/derived images; no comparison square is supplied as an input.
-/
namespace Decoupling.HighDim.Torus
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]

theorem homotopyDualMap_comp {C E F : CochainComplex (ModuleCat R) ℤ}
    (f : (homotopyQuotient R).obj C ⟶ (homotopyQuotient R).obj E)
    (g : (homotopyQuotient R).obj E ⟶ (homotopyQuotient R).obj F) :
    homotopyDualMap R (f ≫ g) = homotopyDualMap R g ≫ homotopyDualMap R f := by
  obtain ⟨f, rfl⟩ := (homotopyQuotient R).map_surjective f
  obtain ⟨g, rfl⟩ := (homotopyQuotient R).map_surjective g
  rw [← Functor.map_comp, homotopyDualMap_quotient, complexDualMap_comp, Functor.map_comp]
  rfl

theorem homotopyDerivedEquiv_map (C E : CochainComplex (ModuleCat R) ℤ)
    [C.IsKProjective] (f : C ⟶ E) :
    homotopyDerivedEquiv C E ((homotopyQuotient R).map f) = DerivedCategory.Q.map f := by
  dsimp [homotopyDerivedEquiv, CategoryTheory.Linear.homCongr]
  have hn := (DerivedCategory.quotientCompQhIso (ModuleCat R)).hom.naturality f
  dsimp only [Functor.comp_map] at hn
  rw [Category.assoc, hn]
  simp

theorem homotopyDerivedEquiv_postcomp (C E F : CochainComplex (ModuleCat R) ℤ)
    [C.IsKProjective]
    (g : (homotopyQuotient R).obj C ⟶ (homotopyQuotient R).obj E) (f : E ⟶ F) :
    homotopyDerivedEquiv C F (g ≫ (homotopyQuotient R).map f) =
      homotopyDerivedEquiv C E g ≫ DerivedCategory.Q.map f := by
  obtain ⟨g, rfl⟩ := (homotopyQuotient R).map_surjective g
  rw [← Functor.map_comp, homotopyDerivedEquiv_map, homotopyDerivedEquiv_map, Functor.map_comp]

theorem homotopyDerivedEquiv_precomp (C E F : CochainComplex (ModuleCat R) ℤ)
    [C.IsKProjective] [E.IsKProjective]
    (f : C ⟶ E) (g : (homotopyQuotient R).obj E ⟶ (homotopyQuotient R).obj F) :
    homotopyDerivedEquiv C F ((homotopyQuotient R).map f ≫ g) =
      DerivedCategory.Q.map f ≫ homotopyDerivedEquiv E F g := by
  obtain ⟨g, rfl⟩ := (homotopyQuotient R).map_surjective g
  rw [← Functor.map_comp, homotopyDerivedEquiv_map, homotopyDerivedEquiv_map, Functor.map_comp]

theorem homotopyDerivedEquiv_symm_postcomp (C E F : CochainComplex (ModuleCat R) ℤ)
    [C.IsKProjective] (g : DerivedCategory.Q.obj C ⟶ DerivedCategory.Q.obj E) (f : E ⟶ F) :
    (homotopyDerivedEquiv C F).symm (g ≫ DerivedCategory.Q.map f) =
      (homotopyDerivedEquiv C E).symm g ≫ (homotopyQuotient R).map f := by
  apply (homotopyDerivedEquiv C F).injective
  rw [LinearEquiv.apply_symm_apply, homotopyDerivedEquiv_postcomp, LinearEquiv.apply_symm_apply]

theorem homotopyDerivedEquiv_symm_precomp (C E F : CochainComplex (ModuleCat R) ℤ)
    [C.IsKProjective] [E.IsKProjective] (f : C ⟶ E)
    (g : DerivedCategory.Q.obj E ⟶ DerivedCategory.Q.obj F) :
    (homotopyDerivedEquiv C F).symm (DerivedCategory.Q.map f ≫ g) =
      (homotopyQuotient R).map f ≫ (homotopyDerivedEquiv E F).symm g := by
  apply (homotopyDerivedEquiv C F).injective
  rw [LinearEquiv.apply_symm_apply, homotopyDerivedEquiv_precomp, LinearEquiv.apply_symm_apply]

variable (K : Type) [Field K] (D : ℕ)

theorem localDualityHomEquiv_naturality
    (C E : CochainComplex (ModuleCat (Laurent K D)) ℤ)
    [∀ n, Module.Finite (Laurent K D) (C.X n)] [∀ n, Module.Free (Laurent K D) (C.X n)]
    [∀ n, Module.Finite (Laurent K D) (E.X n)] [∀ n, Module.Free (Laurent K D) (E.X n)]
    (b c : ℤ) [C.IsStrictlyGE b] [E.IsStrictlyGE c]
    (f : C ⟶ E) (g : probe K D ⟶ DerivedCategory.Q.obj C) :
    localDualityHomEquiv K D E c (g ≫ DerivedCategory.Q.map f) =
      (homotopyQuotient (Laurent K D)).map (complexDualMap (Laurent K D) f) ≫
        localDualityHomEquiv K D C b g := by
  let : (complexDual (Laurent K D) C).IsKProjective :=
    CochainComplex.isKProjective_of_projective _ (-b)
  let : (complexDual (Laurent K D) E).IsKProjective :=
    CochainComplex.isKProjective_of_projective _ (-c)
  dsimp only [probe] at g
  dsimp only [localDualityHomEquiv, LinearEquiv.trans_apply]
  simp only [CategoryTheory.Linear.homCongr_apply, Iso.refl_inv,
    Iso.symm_hom, Category.id_comp]
  have hcongr (Y : Derived K D) (h : probe K D ⟶ Y) :
      CategoryTheory.Linear.homCongr (Laurent K D)
        (coefficientResolutionDualDerivedIso K D).symm (Iso.refl Y) h =
      (coefficientResolutionDualDerivedIso K D).hom ≫ h := by
    change ((coefficientResolutionDualDerivedIso K D).hom ≫ h) ≫ 𝟙 Y = _
    exact Category.comp_id _
  erw [hcongr, hcongr]
  let P := complexDual (Laurent K D) (coefficientResolution K D)
  let eP := coefficientResolutionDualDerivedIso K D
  let eQ := (homotopyQuotient (Laurent K D)).map
    (complexDoubleDualIso (coefficientResolution K D)).inv
  let eF := (Toric.derivedIso K D 0).hom
  change (homotopyDerivedEquiv (complexDual (Laurent K D) E) _).symm
    ((homotopyDerivedEquiv (complexDual (Laurent K D) E) _)
      (homotopyDualMap _ ((homotopyDerivedEquiv P E).symm
        (eP.hom ≫ (g ≫ DerivedCategory.Q.map f))) ≫ eQ) ≫ eF) =
    (homotopyQuotient (Laurent K D)).map (complexDualMap (Laurent K D) f) ≫
    (homotopyDerivedEquiv (complexDual (Laurent K D) C) _).symm
    ((homotopyDerivedEquiv (complexDual (Laurent K D) C) _)
      (homotopyDualMap _ ((homotopyDerivedEquiv P C).symm (eP.hom ≫ g)) ≫ eQ) ≫ eF)
  rw [← Category.assoc eP.hom g, homotopyDerivedEquiv_symm_postcomp,
    homotopyDualMap_comp, homotopyDualMap_quotient]
  rw [Category.assoc, homotopyDerivedEquiv_precomp,
    Category.assoc, homotopyDerivedEquiv_symm_precomp]

end
end Decoupling.HighDim.Torus
