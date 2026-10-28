import Decoupling.HighDim.TorusTensorDual
import Decoupling.HighDim.GluedNativeHomology

/-!
# Naturality of the actual Hom-window homology identification

HD010, Appendix B.3. The map on the left is the genuine native homology
map. Naturality is checked on actual cycle representatives, including
their passage to the homotopy category.
-/
namespace Decoupling.HighDim.Torus
open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R]

def homSingleScMap {C E : CochainComplex (ModuleCat R) ℤ}
    (f : C ⟶ E) (A : ModuleCat R) : homSingleSc E A ⟶ homSingleSc C A where
  τ₁ := ModuleCat.ofHom (CategoryTheory.Linear.leftComp R A (f.f 1))
  τ₂ := ModuleCat.ofHom (CategoryTheory.Linear.leftComp R A (f.f 0))
  τ₃ := ModuleCat.ofHom (CategoryTheory.Linear.leftComp R A (f.f (-1)))
  comm₁₂ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    change C.d 0 1 ≫ f.f 1 ≫ (show E.X 1 ⟶ A from g) =
      f.f 0 ≫ E.d 0 1 ≫ (show E.X 1 ⟶ A from g)
    rw [f.comm_assoc]
  comm₂₃ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    change C.d (-1) 0 ≫ f.f 0 ≫ (show E.X 0 ⟶ A from g) =
      f.f (-1) ≫ E.d (-1) 0 ≫ (show E.X 0 ⟶ A from g)
    rw [f.comm_assoc]

theorem homSingleHomologyEquiv_cycle (C : CochainComplex (ModuleCat R) ℤ)
    (A : ModuleCat R) (f : (homSingleSc C A).X₂) (hf : (homSingleSc C A).g f = 0) :
    homSingleHomologyEquiv C A (Glued.cycleClass (homSingleSc C A) f hf) =
      cyclesToHomSingle C A ⟨f, hf⟩ := by
  have he : (homSingleSc C A).moduleCatHomologyIso.hom
      (Glued.cycleClass (homSingleSc C A) f hf) =
        (homSingleSc C A).moduleCatLeftHomologyData.π ⟨f, hf⟩ := by
    change ((homSingleSc C A).moduleCatCyclesIso.inv ≫
      (homSingleSc C A).homologyπ ≫ (homSingleSc C A).moduleCatHomologyIso.hom) ⟨f, hf⟩ = _
    rw [ShortComplex.π_moduleCatCyclesIso_hom]
    simp
  change (cyclesToHomSingle C A).quotKerEquivOfSurjective (cyclesToHomSingle_surjective C A)
    ((Submodule.quotEquivOfEq _ _ _)
      ((homSingleSc C A).moduleCatHomologyIso.hom (Glued.cycleClass _ f hf))) = _
  rw [he]
  rfl

theorem homSingleCycle_precompose {C E : CochainComplex (ModuleCat R) ℤ}
    (f : C ⟶ E) (A : ModuleCat R) (g : E.X 0 ⟶ A)
    (hg : E.d (-1) 0 ≫ g = 0) :
    Cocycle.homOf (homSingleCycle C A ⟨f.f 0 ≫ g, by
      change C.d (-1) 0 ≫ f.f 0 ≫ g = 0
      rw [← f.comm_assoc, hg, comp_zero]⟩) =
      f ≫ Cocycle.homOf (homSingleCycle E A ⟨g, hg⟩) := by
  apply HomologicalComplex.to_single_hom_ext
  rfl

theorem homSingleHomologyEquiv_naturality {C E : CochainComplex (ModuleCat R) ℤ}
    (f : C ⟶ E) (A : ModuleCat R) (x : (homSingleSc E A).homology) :
    homSingleHomologyEquiv C A (ShortComplex.homologyMap (homSingleScMap f A) x) =
      (homotopyQuotient R).map f ≫ homSingleHomologyEquiv E A x := by
  obtain ⟨g, hg, rfl⟩ := Glued.cycleClass_surjective _ x
  rw [Glued.homologyMap_cycleClass, homSingleHomologyEquiv_cycle,
    homSingleHomologyEquiv_cycle]
  change (homotopyQuotient R).map (Cocycle.homOf _) =
    (homotopyQuotient R).map f ≫ (homotopyQuotient R).map (Cocycle.homOf _)
  rw [← Functor.map_comp]
  congr 1
  exact homSingleCycle_precompose f A g hg

end
end Decoupling.HighDim.Torus
