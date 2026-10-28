import Decoupling.HighDim.AlgorithmTwoComparisonLift
import Decoupling.HighDim.TorusTensorMapsClasses

/-!
# Normalisation through an actual zero-differential cochain model

This avoids a choice of grouping for repeated toric degrees. The
termwise isomorphisms of the zero-differential model give an actual
cochain automorphism, and localisation transports it to the supplied
formal complex. All homology coordinate equalities are native ones.
-/
namespace Decoupling.HighDim.AlgorithmTwoComparison
open CategoryTheory HomologicalComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
attribute [local instance] HasDerivedCategory.standard
variable {R : Type} [CommRing R]
variable (V : CochainComplex (ModuleCat R) ℤ) (hz : ∀ i j, V.d i j = 0)

def zeroClassIso (n : ℤ) : V.X n ≅ V.homology n := by
  let S := V.sc' (n - 1) n (n + 1)
  let f := Torus.zeroDifferentialClass S (hz n (n + 1))
  have hf : Function.Bijective f := Torus.zeroDifferentialClass_bijective S
    (hz (n - 1) n) (hz n (n + 1))
  let := (ConcreteCategory.isIso_iff_bijective f).mpr hf
  exact asIso f ≪≫ (cycleHomologyIso V n).symm

theorem zeroClassIso_apply (n : ℤ) (x : V.X n) :
    (zeroClassIso V hz n).hom x = nativeCycleClass V n x (by rw [hz]; rfl) := rfl

def zeroDegreewiseIso (a : ∀ n, V.X n ≅ V.X n) : V ≅ V :=
  HomologicalComplex.Hom.isoOfComponents a (by intro i j hij; simp [hz])

theorem zeroDegreewiseIso_homology (a : ∀ n, V.X n ≅ V.X n) (n : ℤ) :
    (zeroClassIso V hz n).hom ≫ homologyMap (zeroDegreewiseIso V hz a).hom n =
      (a n).hom ≫ (zeroClassIso V hz n).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change homologyMap (zeroDegreewiseIso V hz a).hom n ((zeroClassIso V hz n).hom x) =
    (zeroClassIso V hz n).hom ((a n).hom x)
  rw [zeroClassIso_apply, nativeCycleClass_naturality, zeroClassIso_apply]
  rfl

def zeroDerivedCoordinates (n : ℤ) :
    V.X n ≅ (DerivedCategory.homologyFunctor (ModuleCat R) n).obj (DerivedCategory.Q.obj V) :=
  zeroClassIso V hz n ≪≫ ((DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app V).symm

theorem zeroDerivedCoordinates_naturality (a : ∀ n, V.X n ≅ V.X n) (n : ℤ) :
    (zeroDerivedCoordinates V hz n).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) n).map
        (DerivedCategory.Q.map (zeroDegreewiseIso V hz a).hom) =
      (a n).hom ≫ (zeroDerivedCoordinates V hz n).hom := by
  have hn := (DerivedCategory.homologyFunctorFactors (ModuleCat R) n).inv.naturality
    (zeroDegreewiseIso V hz a).hom
  change homologyMap (zeroDegreewiseIso V hz a).hom n ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app V).inv =
    ((DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app V).inv ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) n).map
        (DerivedCategory.Q.map (zeroDegreewiseIso V hz a).hom) at hn
  dsimp only [zeroDerivedCoordinates, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, ← hn, ← Category.assoc, zeroDegreewiseIso_homology, Category.assoc]

variable {C : CochainComplex (ModuleCat R) ℤ}
  (e : DerivedCategory.Q.obj V ≅ DerivedCategory.Q.obj C)
  (b : ∀ n, V.X n ≅ C.homology n)

def oldZeroCoordinates (n : ℤ) : V.X n ≅ C.homology n :=
  zeroDerivedCoordinates V hz n ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) n).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app C

def zeroNormalizedIso : DerivedCategory.Q.obj V ≅ DerivedCategory.Q.obj C :=
  DerivedCategory.Q.mapIso (zeroDegreewiseIso V hz (fun n => b n ≪≫
    (oldZeroCoordinates V hz e n).symm)) ≪≫ e

theorem zeroNormalizedIso_homology (n : ℤ) :
    (zeroDerivedCoordinates V hz n).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) n).map (zeroNormalizedIso V hz e b).hom ≫
        ((DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app C).hom = (b n).hom := by
  dsimp only [zeroNormalizedIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [Functor.map_comp, ← Category.assoc, ← Category.assoc, zeroDerivedCoordinates_naturality]
  let old := oldZeroCoordinates V hz e n
  change (((b n).hom ≫ old.inv) ≫ (zeroDerivedCoordinates V hz n).hom) ≫
    (DerivedCategory.homologyFunctor (ModuleCat R) n).map e.hom ≫
      ((DerivedCategory.homologyFunctorFactors (ModuleCat R) n).app C).hom = _
  rw [Category.assoc]
  change ((b n).hom ≫ old.inv) ≫ old.hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end
end Decoupling.HighDim.AlgorithmTwoComparison
