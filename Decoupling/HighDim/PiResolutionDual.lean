import Decoupling.HighDim.PiResolution

/-!
# Finite sums of genuine positive derived Hom profiles

The comparison is an isomorphism of full complexes, followed by the actual
extension, good truncation, and derived localization functors. It retains
all attachment data rather than comparing only cohomology groups.
-/

namespace Decoupling.HighDim.PiResolution

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
noncomputable section
attribute [local instance] Classical.propDecidable HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] {ι : Type} [Fintype ι]
  {X : ι → ModuleCat R} (P : ∀ i, ProjectiveResolution (X i)) (Y : ModuleCat R)

local instance : HasFiniteBiproducts (CochainComplex (ModuleCat R) ℕ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

def dualCoordinates (n : ℕ) :
    (ResolutionCohomology.dualComplex (resolution P) Y).X n ≃ₗ[R]
      (∀ i, (ResolutionCohomology.dualComplex (P i) Y).X n) :=
  ModuleCat.homLinearEquiv.trans
    ((LinearMap.lsum R (fun i => (P i).complex.X n) R).symm.trans
      (LinearEquiv.piCongrRight (fun _ => ModuleCat.homLinearEquiv.symm)))

@[simp] theorem dualCoordinates_apply (n : ℕ)
    (f : (complex P).X n ⟶ Y)
    (i : ι) (v : (P i).complex.X n) :
    (show (P i).complex.X n ⟶ Y from dualCoordinates P Y n f i) v = f (Pi.single i v) := rfl

omit [Fintype ι] in
theorem differential_single (n : ℕ) (i : ι) (v : (P i).complex.X (n + 1)) :
    differential P n (Pi.single i v) = Pi.single i ((P i).complex.d (n + 1) n v) := by
  funext j
  change (P j).complex.d (n + 1) n ((Pi.single i v : ∀ i, (P i).complex.X (n + 1)) j) = _
  by_cases h : j = i
  · subst j
    simp
  · simp [Pi.single_eq_of_ne h]

theorem dualCoordinates_d (n : ℕ)
    (f : (complex P).X n ⟶ Y) (i : ι) :
    dualCoordinates P Y (n + 1)
        ((ResolutionCohomology.dualComplex (resolution P) Y).d n (n + 1) f) i =
      (ResolutionCohomology.dualComplex (P i) Y).d n (n + 1) (dualCoordinates P Y n f i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  change f ((complex P).d (n + 1) n (Pi.single i v)) =
    f (Pi.single i ((P i).complex.d (n + 1) n v))
  apply congrArg f
  simpa [complex] using differential_single P n i v

def dualSum : CochainComplex (ModuleCat R) ℕ :=
  ⨁ fun i => ResolutionCohomology.dualComplex (P i) Y

def dualSumTermIso (n : ℕ) : (dualSum P Y).X n ≅
    ModuleCat.of R (∀ i, (ResolutionCohomology.dualComplex (P i) Y).X n) :=
  (eval (ModuleCat R) (ComplexShape.up ℕ) n).mapBiproduct
    (fun i => ResolutionCohomology.dualComplex (P i) Y) ≪≫
      ModuleCat.biproductIsoPi (fun i => (ResolutionCohomology.dualComplex (P i) Y).X n)

theorem dualSumTermIso_hom_proj (n : ℕ) (i : ι) :
    (dualSumTermIso P Y n).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
      (biproduct.π (fun i => ResolutionCohomology.dualComplex (P i) Y) i).f n := by
  have h : (ModuleCat.biproductIsoPi
      (fun i => (ResolutionCohomology.dualComplex (P i) Y).X n)).hom ≫
        ModuleCat.ofHom (LinearMap.proj i) =
      biproduct.π (fun i => (ResolutionCohomology.dualComplex (P i) Y).X n) i := by
    rw [← cancel_epi (ModuleCat.biproductIsoPi
      (fun i => (ResolutionCohomology.dualComplex (P i) Y).X n)).inv]
    simp
  simp only [dualSumTermIso, Iso.trans_hom, Category.assoc, h, Functor.mapBiproduct_hom]
  exact biproduct.lift_π _ i

theorem dualSumTermIso_apply (n : ℕ) (v : (dualSum P Y).X n) (i : ι) :
    (dualSumTermIso P Y n).hom v i =
      (biproduct.π (fun i => ResolutionCohomology.dualComplex (P i) Y) i).f n v :=
  congrArg (fun f => f v) (dualSumTermIso_hom_proj P Y n i)

theorem dualSumTermIso_d (n m : ℕ) (v : (dualSum P Y).X n) (i : ι) :
    (dualSumTermIso P Y m).hom ((dualSum P Y).d n m v) i =
      (ResolutionCohomology.dualComplex (P i) Y).d n m ((dualSumTermIso P Y n).hom v i) := by
  rw [dualSumTermIso_apply, dualSumTermIso_apply]
  exact congrArg (fun f => f v)
    ((biproduct.π (fun i => ResolutionCohomology.dualComplex (P i) Y) i).comm n m).symm

def dualSumIso : ResolutionCohomology.dualComplex (resolution P) Y ≅ dualSum P Y :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (dualCoordinates P Y n).toModuleIso ≪≫ (dualSumTermIso P Y n).symm)
    (fun n m hnm => by
      change n + 1 = m at hnm
      subst m
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      apply (dualSumTermIso P Y (n + 1)).toLinearEquiv.injective
      funext i
      change (dualSumTermIso P Y (n + 1)).hom
        ((dualSum P Y).d n (n + 1)
          ((dualSumTermIso P Y n).inv (dualCoordinates P Y n f))) i =
        (dualSumTermIso P Y (n + 1)).hom ((dualSumTermIso P Y (n + 1)).inv
          (dualCoordinates P Y (n + 1)
            ((ResolutionCohomology.dualComplex (resolution P) Y).d n (n + 1) f))) i
      rw [dualSumTermIso_d]
      simp only [Iso.inv_hom_id_apply]
      exact (dualCoordinates_d P Y n f i).symm)

local instance truncGEFunctor_additive :
    ((ComplexShape.embeddingUpIntGE 1).truncGEFunctor (ModuleCat R)).Additive where
  map_add {C T} f g := by
    apply (cancel_epi (C.πTruncGE (ComplexShape.embeddingUpIntGE 1))).mp
    dsimp only [ComplexShape.Embedding.truncGEFunctor]
    simp only [Preadditive.comp_add, HomologicalComplex.πTruncGE_naturality,
      Preadditive.add_comp]

/-- Full positive RHom commutes with these finite products of resolutions. -/
def profileBiproductIso : Profile.ofResolution (resolution P) Y ≅
    ⨁ fun i => Profile.ofResolution (P i) Y := by
  let F := ComplexShape.embeddingUpNat.extendFunctor (ModuleCat R) ⋙
    (ComplexShape.embeddingUpIntGE 1).truncGEFunctor (ModuleCat R) ⋙
      DerivedCategory.Q
  let : F.Additive := by dsimp [F]; infer_instance
  exact F.mapIso (dualSumIso P Y) ≪≫
    F.mapBiproduct (fun i => ResolutionCohomology.dualComplex (P i) Y)

end
end Decoupling.HighDim.PiResolution
