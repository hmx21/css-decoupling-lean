import Decoupling.HighDim.TorusNaturalityHomSingle
import Decoupling.HighDim.TorusNaturalityDual

/-!
# Natural tensor evaluation on actual homology

HD010 Appendix B.3. Tensoring a cochain map and then taking homology
agrees with postcomposition by its actual derived image under local
duality. The statement applies to shifted target complexes as well.
-/
namespace Decoupling.HighDim.Torus
open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

def tensorWindowMap {C E : CochainComplex (ModuleCat R) ℤ} (f : C ⟶ E) :
    (C.sc' (-1) 0 1).map (extensionRestricted φ) ⟶
      (E.sc' (-1) 0 1).map (extensionRestricted φ) :=
  (extensionRestricted φ).mapShortComplex.map
    ((shortComplexFunctor' (ModuleCat R) (.up ℤ) (-1) 0 1).map f)

theorem tensorDualWindowIso_naturality
    {C E : CochainComplex (ModuleCat R) ℤ}
    [∀ n, Module.Finite R (C.X n)] [∀ n, Module.Free R (C.X n)]
    [∀ n, Module.Finite R (E.X n)] [∀ n, Module.Free R (E.X n)] (f : C ⟶ E) :
    tensorWindowMap φ f ≫ (tensorDualWindowIso φ E).hom =
      (tensorDualWindowIso φ C).hom ≫ homSingleScMap (complexDualMap R f) (scalarTarget φ) := by
  apply ShortComplex.hom_ext
  · exact extensionDualEquiv_naturality φ (f.f (-1))
  · exact extensionDualEquiv_naturality φ (f.f 0)
  · exact extensionDualEquiv_naturality φ (f.f 1)

theorem tensorWindowHomEquiv_naturality
    {C E : CochainComplex (ModuleCat R) ℤ}
    [∀ n, Module.Finite R (C.X n)] [∀ n, Module.Free R (C.X n)]
    [∀ n, Module.Finite R (E.X n)] [∀ n, Module.Free R (E.X n)]
    (f : C ⟶ E) (x : ((C.sc' (-1) 0 1).map (extensionRestricted φ)).homology) :
    homSingleHomologyEquiv (complexDual R E) (scalarTarget φ)
      (ShortComplex.homologyMap (tensorDualWindowIso φ E).hom
        (ShortComplex.homologyMap (tensorWindowMap φ f) x)) =
      (homotopyQuotient R).map (complexDualMap R f) ≫
        homSingleHomologyEquiv (complexDual R C) (scalarTarget φ)
          (ShortComplex.homologyMap (tensorDualWindowIso φ C).hom x) := by
  have he := congrArg (fun g => ShortComplex.homologyMap g)
    (tensorDualWindowIso_naturality φ f)
  simp only [ShortComplex.homologyMap_comp] at he
  have he' := congrArg (fun g => g x) he
  change ShortComplex.homologyMap (tensorDualWindowIso φ E).hom
    (ShortComplex.homologyMap (tensorWindowMap φ f) x) =
    ShortComplex.homologyMap (homSingleScMap (complexDualMap R f) (scalarTarget φ))
      (ShortComplex.homologyMap (tensorDualWindowIso φ C).hom x) at he'
  rw [he', homSingleHomologyEquiv_naturality]

theorem tensorHomologyHomEquiv_naturality
    {C E : CochainComplex (ModuleCat R) ℤ}
    [∀ n, Module.Finite R (C.X n)] [∀ n, Module.Free R (C.X n)]
    [∀ n, Module.Finite R (E.X n)] [∀ n, Module.Free R (E.X n)]
    (f : C ⟶ E)
    (x : (((extensionRestricted φ).mapHomologicalComplex (.up ℤ)).obj C).homology 0) :
    tensorHomologyHomEquiv φ E
      (HomologicalComplex.homologyMap
        (((extensionRestricted φ).mapHomologicalComplex (.up ℤ)).map f) 0 x) =
      (homotopyQuotient R).map (complexDualMap R f) ≫ tensorHomologyHomEquiv φ C x := by
  let F := (extensionRestricted φ).mapHomologicalComplex (.up ℤ)
  have he : HomologicalComplex.homologyMap (F.map f) 0 ≫
      ((F.obj E).homologyIsoSc' (-1) 0 1 (by simp) (by simp)).hom =
      ((F.obj C).homologyIsoSc' (-1) 0 1 (by simp) (by simp)).hom ≫
        ShortComplex.homologyMap (tensorWindowMap φ f) :=
    (homologyFunctorIso' (ModuleCat R) (.up ℤ) (-1) 0 1
      (by simp) (by simp)).hom.naturality (F.map f)
  have hx := congrArg (fun u => u x) he
  change ((F.obj E).homologyIsoSc' (-1) 0 1 (by simp) (by simp)).hom
    (HomologicalComplex.homologyMap (F.map f) 0 x) =
    ShortComplex.homologyMap (tensorWindowMap φ f)
      (((F.obj C).homologyIsoSc' (-1) 0 1 (by simp) (by simp)).hom x) at hx
  change homSingleHomologyEquiv (complexDual R E) (scalarTarget φ)
    (ShortComplex.homologyMap (tensorDualWindowIso φ E).hom
      (((F.obj E).homologyIsoSc' (-1) 0 1 (by simp) (by simp)).hom
        (HomologicalComplex.homologyMap (F.map f) 0 x))) = _
  rw [hx, tensorWindowHomEquiv_naturality]
  rfl

variable (K : Type) [Field K] (D : ℕ)

/-- A natural local-duality bridge with actual scalar-extended homology
on its source, retained as a Laurent module before forgetting scalars. -/
def tensorNativeEquiv (C : CochainComplex (ModuleCat (Laurent K D)) ℤ)
    [∀ n, Module.Finite (Laurent K D) (C.X n)]
    [∀ n, Module.Free (Laurent K D) (C.X n)] (b : ℤ) [C.IsStrictlyGE b] :
    (((extensionRestricted (augmentation : Laurent K D →+* K)).mapHomologicalComplex
      (.up ℤ)).obj C).homology 0 ≃ₗ[Laurent K D]
        (probe K D ⟶ DerivedCategory.Q.obj C) :=
  (tensorHomologyHomEquiv augmentation C).trans (localDualityHomEquiv K D C b).symm

theorem tensorNativeEquiv_naturality
    (C E : CochainComplex (ModuleCat (Laurent K D)) ℤ)
    [∀ n, Module.Finite (Laurent K D) (C.X n)] [∀ n, Module.Free (Laurent K D) (C.X n)]
    [∀ n, Module.Finite (Laurent K D) (E.X n)] [∀ n, Module.Free (Laurent K D) (E.X n)]
    (b c : ℤ) [C.IsStrictlyGE b] [E.IsStrictlyGE c] (f : C ⟶ E)
    (x : (((extensionRestricted (augmentation : Laurent K D →+* K)).mapHomologicalComplex
      (.up ℤ)).obj C).homology 0) :
    tensorNativeEquiv K D E c (HomologicalComplex.homologyMap
      (((extensionRestricted augmentation).mapHomologicalComplex (.up ℤ)).map f) 0 x) =
      tensorNativeEquiv K D C b x ≫ DerivedCategory.Q.map f := by
  apply (localDualityHomEquiv K D E c).injective
  change (localDualityHomEquiv K D E c)
    ((localDualityHomEquiv K D E c).symm _) = _
  rw [LinearEquiv.apply_symm_apply, localDualityHomEquiv_naturality K D C E b c f]
  change tensorHomologyHomEquiv augmentation E _ =
    _ ≫ (localDualityHomEquiv K D C b) ((localDualityHomEquiv K D C b).symm _)
  rw [LinearEquiv.apply_symm_apply, tensorHomologyHomEquiv_naturality]
  rfl

end
end Decoupling.HighDim.Torus
