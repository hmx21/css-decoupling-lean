import Decoupling.HighDim.AlgorithmTwoComparisonNormalization
import Decoupling.HighDim.AlgorithmTwoComparisonCocycles
import Decoupling.HighDim.TorusNaturalityDual

/-!
# An actual cochain comparison with prescribed native homology maps

K-projective localisation is used only to prove that the prescribed
cochain equations are solvable. The resulting map is identified by its
actual image under Q, and its maps on native homology are exactly the
specified isomorphisms. This is a mathematical solvability result,
not an operational cost attributed to classical choice.
-/
namespace Decoupling.HighDim.AlgorithmTwoComparison
open CategoryTheory HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
attribute [local instance] HasDerivedCategory.standard
variable {R : Type} [CommRing R]
variable {T C : CochainComplex (ModuleCat R) ℤ}

theorem exists_cochain_lift [T.IsKProjective]
    (f : DerivedCategory.Q.obj T ⟶ DerivedCategory.Q.obj C) :
    ∃ g : T ⟶ C, DerivedCategory.Q.map g = f := by
  obtain ⟨g, hg⟩ := (Torus.homotopyQuotient R).map_surjective
    ((Torus.homotopyDerivedEquiv T C).symm f)
  refine ⟨g, ?_⟩
  rw [← Torus.homotopyDerivedEquiv_map, hg, LinearEquiv.apply_symm_apply]

variable {ι : Type} [Fintype ι] {degree : ι → ℤ} {E : ι → ModuleCat R}
  (hinj : Function.Injective degree)
  (eT : DerivedCategory.Q.obj T ≅ formalSum degree E)
  (eC : formalSum degree E ≅ DerivedCategory.Q.obj C)
  (b : ∀ i, E i ≅ C.homology (degree i))

def sourceLayerIso (i : ι) : E i ≅ T.homology (degree i) :=
  layerInclusionIso degree E hinj i ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) (degree i)).mapIso eT.symm ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) (degree i)).app T

def desiredDerivedIso : DerivedCategory.Q.obj T ≅ DerivedCategory.Q.obj C :=
  eT ≪≫ normalizedIso hinj eC (fun i => b i ≪≫
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) (degree i)).app C).symm)

theorem lifted_homology (g : T ⟶ C)
    (hg : DerivedCategory.Q.map g = (desiredDerivedIso hinj eT eC b).hom) (i : ι) :
    (sourceLayerIso hinj eT i).hom ≫ homologyMap g (degree i) = (b i).hom := by
  let H := DerivedCategory.homologyFunctor (ModuleCat R) (degree i)
  let F := DerivedCategory.homologyFunctorFactors (ModuleCat R) (degree i)
  have hn : H.map (DerivedCategory.Q.map g) ≫ (F.app C).hom =
      (F.app T).hom ≫ homologyMap g (degree i) := F.hom.naturality g
  change ((layerInclusionIso degree E hinj i).hom ≫ H.map eT.inv ≫ (F.app T).hom) ≫
    homologyMap g (degree i) = _
  simp only [Category.assoc]
  rw [← hn]
  rw [← Category.assoc (H.map eT.inv), ← H.map_comp, hg]
  have hcancel : eT.inv ≫ (desiredDerivedIso hinj eT eC b).hom =
      (normalizedIso hinj eC (fun i => b i ≪≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat R) (degree i)).app C).symm)).hom := by
    simp [desiredDerivedIso]
  rw [hcancel, ← Category.assoc, normalizedIso_homology]
  change ((b i).hom ≫ (F.app C).inv) ≫ (F.app C).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The normalised native isomorphism is represented by a genuine
quasi-isomorphism, with the required map on every supported layer. -/
theorem exists_normalized_cochain [T.IsKProjective] :
    ∃ g : T ⟶ C, QuasiIso g ∧
      DerivedCategory.Q.map g = (desiredDerivedIso hinj eT eC b).hom ∧
      ∀ i, (sourceLayerIso hinj eT i).hom ≫ homologyMap g (degree i) = (b i).hom := by
  obtain ⟨g, hg⟩ := exists_cochain_lift (desiredDerivedIso hinj eT eC b).hom
  have hq : QuasiIso g := by
    apply (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat R) g).mp
    rw [hg]
    infer_instance
  exact ⟨g, hq, hg, lifted_homology hinj eT eC b g hg⟩

/-- Supplied finite free coordinates and the actual upper degree bound
discharge K-projectivity; it is not an extra input to the algorithm. -/
theorem exists_normalized_cochain_of_coordinates (cT : StableFree.Coordinates T)
    (upper : ℤ) [T.IsStrictlyLE upper] :
    ∃ g : T ⟶ C, QuasiIso g ∧
      DerivedCategory.Q.map g = (desiredDerivedIso hinj eT eC b).hom ∧
      ∀ i, (sourceLayerIso hinj eT i).hom ≫ homologyMap g (degree i) = (b i).hom := by
  let (j : ℤ) : Module.Free R (T.X j) := Module.Free.of_equiv (cT.equiv j).symm
  let (j : ℤ) : Projective (T.X j) := inferInstance
  let : T.IsKProjective := CochainComplex.isKProjective_of_projective T upper
  exact exists_normalized_cochain hinj eT eC b

end
end Decoupling.HighDim.AlgorithmTwoComparison
