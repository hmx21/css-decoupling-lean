import Decoupling.HighDim.AlgorithmTwoComparisonCorrection
import Decoupling.HighDim.FiniteBiproduct
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Normalising a formal derived isomorphism on its native homology

This is the change-of-basis step in Appendix C1. The degree indices
are distinct, so homology sees exactly one diagonal summand. A given
formal isomorphism can therefore be modified to induce any specified
module isomorphisms in each supported degree.
-/
namespace Decoupling.HighDim.AlgorithmTwoComparison
open CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
universe u
noncomputable section

section Additive
variable {A B : Type*} [Category* A] [Category* B] [Preadditive A] [Preadditive B]
  [HasFiniteBiproducts A] {ι : Type} [Fintype ι]

/-- An additive functor which kills the other summands identifies the
remaining summand with the image of the actual biproduct. -/
def mapBiproductInclusionIso (F : A ⥤ B) [F.Additive] (M : ι → A) (j : ι)
    (hz : ∀ k, k ≠ j → IsZero (F.obj (M k))) :
    F.obj (M j) ≅ F.obj (⨁ M) where
  hom := F.map (biproduct.ι M j)
  inv := F.map (biproduct.π M j)
  hom_inv_id := by rw [← F.map_comp, biproduct.ι_π_self, F.map_id]
  inv_hom_id := by
    classical
    rw [← F.map_comp]
    have he : (∑ k, F.map (biproduct.π M k ≫ biproduct.ι M k)) =
        F.map (biproduct.π M j ≫ biproduct.ι M j) := by
      apply Finset.sum_eq_single j
      · intro k _ hkj
        rw [F.map_comp, (hz k hkj).eq_of_tgt (F.map (biproduct.π M k)) 0,
          zero_comp]
      · simp
    rw [← he, ← F.map_sum, biproduct.total, F.map_id]

end Additive

variable {R : Type u} [CommRing R]
attribute [local instance] HasDerivedCategory.standard
variable {ι : Type} [Fintype ι] (degree : ι → ℤ) (E : ι → ModuleCat.{u} R)

def singleFamily (i : ι) : DerivedCategory (ModuleCat.{u} R) :=
  (DerivedCategory.singleFunctor (ModuleCat R) (degree i)).obj (E i)

def formalSum : DerivedCategory (ModuleCat.{u} R) := ⨁ singleFamily degree E

def layerInclusionIso (hinj : Function.Injective degree) (j : ι) :
    E j ≅ (DerivedCategory.homologyFunctor (ModuleCat R) (degree j)).obj (formalSum degree E) :=
  ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat R) (degree j)).app (E j)).symm ≪≫
    mapBiproductInclusionIso (DerivedCategory.homologyFunctor (ModuleCat R) (degree j))
      (singleFamily degree E) j (by
        intro k hkj
        change IsZero ((DerivedCategory.homologyFunctor (ModuleCat R) (degree j)).obj
          ((DerivedCategory.singleFunctor (ModuleCat R) (degree k)).obj (E k)))
        have hne : degree j ≠ degree k := fun h => hkj (hinj h.symm)
        rcases lt_or_gt_of_ne hne with hlt | hgt
        · exact DerivedCategory.isZero_of_isGE _ (degree k) (degree j) hlt
        · exact DerivedCategory.isZero_of_isLE _ (degree k) (degree j) hgt)

variable {degree E}

def diagonalIso (a : ∀ i, E i ≅ E i) : formalSum degree E ≅ formalSum degree E :=
  biproduct.mapIso (fun i => (DerivedCategory.singleFunctor (ModuleCat R) (degree i)).mapIso (a i))

theorem diagonal_homology (hinj : Function.Injective degree) (a : ∀ i, E i ≅ E i) (j : ι) :
    (layerInclusionIso degree E hinj j).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) (degree j)).map (diagonalIso a).hom =
    (a j).hom ≫ (layerInclusionIso degree E hinj j).hom := by
  dsimp only [layerInclusionIso, Iso.trans_hom, Iso.symm_hom, mapBiproductInclusionIso]
  rw [Category.assoc, ← Functor.map_comp]
  have hι : biproduct.ι (singleFamily degree E) j ≫ (diagonalIso a).hom =
      (DerivedCategory.singleFunctor (ModuleCat R) (degree j)).map (a j).hom ≫
        biproduct.ι (singleFamily degree E) j := by
    simp [diagonalIso, biproduct.ι_map]
  rw [hι, Functor.map_comp, ← Category.assoc]
  have hn := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat R) (degree j)).inv.naturality (a j).hom
  dsimp only [Functor.id_map, Functor.comp_map] at hn
  dsimp only [Iso.app_inv]
  dsimp only [singleFamily] at *
  rw [← hn, Category.assoc]

variable (hinj : Function.Injective degree) {X : DerivedCategory (ModuleCat.{u} R)}
  (e : formalSum degree E ≅ X)
  (b : ∀ i, E i ≅ (DerivedCategory.homologyFunctor (ModuleCat R) (degree i)).obj X)

/-- Change of coordinates is explicitly diagonal on the single layers. -/
def normalizingCoordinates (i : ι) : E i ≅ E i :=
  b i ≪≫ ((layerInclusionIso degree E hinj i) ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) (degree i)).mapIso e).symm

def normalizedIso : formalSum degree E ≅ X :=
  diagonalIso (normalizingCoordinates hinj e b) ≪≫ e

/-- Exact native homology effect, including the originally specified
module coordinates, rather than just invertibility or vanishing. -/
theorem normalizedIso_homology (j : ι) :
    (layerInclusionIso degree E hinj j).hom ≫
      (DerivedCategory.homologyFunctor (ModuleCat R) (degree j)).map
        (normalizedIso hinj e b).hom = (b j).hom := by
  dsimp only [normalizedIso, Iso.trans_hom]
  rw [Functor.map_comp, ← Category.assoc, diagonal_homology, Category.assoc]
  change (normalizingCoordinates hinj e b j).hom ≫
    ((layerInclusionIso degree E hinj j) ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat R) (degree j)).mapIso e).hom = _
  let old := (layerInclusionIso degree E hinj j) ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat R) (degree j)).mapIso e
  change ((b j).hom ≫ old.inv) ≫ old.hom = _
  rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end
end Decoupling.HighDim.AlgorithmTwoComparison
