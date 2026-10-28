import Decoupling.HighDim.TorusHomSingle
import Mathlib.LinearAlgebra.Contraction

/-!
# Tensor evaluation on finite free modules and the actual CSS window

Scalar extension of a finite free module is naturally the module of
linear maps from its dual to the new coefficient ring. The comparison
uses actual tensor products and the finite-projective evaluation theorem.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits HomologicalComplex TensorProduct
open scoped ChangeOfRings
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)

abbrev extensionRestricted := ModuleCat.extendScalars φ ⋙ ModuleCat.restrictScalars φ

abbrev scalarTarget := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S)

/-- The genuine tensor-Hom evaluation equivalence for a finite free
module; no chosen basis enters the map. -/
def extensionDualEquiv (M : ModuleCat R) [Module.Finite R M] [Module.Free R M] :
    (extensionRestricted φ).obj M ≃ₗ[R]
      (ModuleCat.of R (Module.Dual R M) ⟶ scalarTarget φ) := by
  letI : Algebra R S := φ.toAlgebra
  exact (TensorProduct.comm R S M).trans
    ((TensorProduct.congr (Module.evalEquiv R M) (LinearEquiv.refl R S)).trans
      ((dualTensorHomEquiv R (Module.Dual R M) S).trans
        (ModuleCat.homLinearEquiv (R := R)
          (M := ModuleCat.of R (Module.Dual R M)) (N := scalarTarget φ)).symm))

theorem extensionDualEquiv_tmul (M : ModuleCat R) [Module.Finite R M] [Module.Free R M]
    (a : S) (x : M) (l : Module.Dual R M) :
    (extensionDualEquiv φ M (a ⊗ₜ[R,φ] x)).hom l = φ (l x) * a := by
  let : Algebra R S := φ.toAlgebra
  rfl

theorem extensionDualEquiv_naturality {M N : ModuleCat R}
    [Module.Finite R M] [Module.Free R M] [Module.Finite R N] [Module.Free R N]
    (f : M ⟶ N) :
    (extensionRestricted φ).map f ≫ (extensionDualEquiv φ N).toModuleIso.hom =
      (extensionDualEquiv φ M).toModuleIso.hom ≫
        ModuleCat.ofHom (CategoryTheory.Linear.leftComp R (scalarTarget φ)
          (ModuleCat.ofHom f.hom.dualMap)) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro t
  let : Algebra R S := φ.toAlgebra
  induction t using TensorProduct.inductionOn with
  | tmul a x =>
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro l
    change (extensionDualEquiv φ N
      ((ModuleCat.extendScalars φ).map f (a ⊗ₜ[R,φ] x))).hom l =
      (extensionDualEquiv φ M (a ⊗ₜ[R,φ] x)).hom (f.hom.dualMap l)
    rw [ModuleCat.ExtendScalars.map_tmul, extensionDualEquiv_tmul, extensionDualEquiv_tmul]
    rfl
  | add t u ht hu => simp only [map_add]; rw [ht, hu]

/-- Tensor evaluation intertwines both differentials of the actual
degree-zero homology window. -/
def tensorDualWindowIso (C : CochainComplex (ModuleCat R) ℤ)
    [∀ n, Module.Finite R (C.X n)] [∀ n, Module.Free R (C.X n)] :
    (C.sc' (-1) 0 1).map (extensionRestricted φ) ≅
      homSingleSc (complexDual R C) (scalarTarget φ) :=
  ShortComplex.isoMk
    (extensionDualEquiv φ (C.X (-1))).toModuleIso
    (extensionDualEquiv φ (C.X 0)).toModuleIso
    (extensionDualEquiv φ (C.X 1)).toModuleIso
    (extensionDualEquiv_naturality φ (C.d (-1) 0)).symm
    (extensionDualEquiv_naturality φ (C.d 0 1)).symm

/-- Actual tensor homology computes actual homotopy classes of maps from
the ordinary dual to the coefficient module. -/
def tensorHomologyHomEquiv (C : CochainComplex (ModuleCat R) ℤ)
    [∀ n, Module.Finite R (C.X n)] [∀ n, Module.Free R (C.X n)] :
    (((extensionRestricted φ).mapHomologicalComplex (.up ℤ)).obj C).homology 0 ≃ₗ[R]
      ((homotopyQuotient R).obj (complexDual R C) ⟶
        (homotopyQuotient R).obj (targetSingle (scalarTarget φ))) :=
  ((((extensionRestricted φ).mapHomologicalComplex (.up ℤ)).obj C).homologyIsoSc'
    (-1) 0 1 (by simp) (by simp)).toLinearEquiv.trans
    (((ShortComplex.homologyFunctor (ModuleCat R)).mapIso
      (tensorDualWindowIso φ C)).toLinearEquiv.trans
        (homSingleHomologyEquiv (complexDual R C) (scalarTarget φ)))

end
end Decoupling.HighDim.Torus
