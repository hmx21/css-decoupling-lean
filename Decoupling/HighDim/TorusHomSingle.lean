import Decoupling.HighDim.TorusLocalDuality
import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle

/-!
# Actual morphisms into a single complex as cycles modulo boundaries

For every cochain complex, homotopy classes of maps into a module in
degree zero are the homology of the three ordinary Hom modules around
that degree. No projectivity or splitting is required for this statement.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open CochainComplex.HomComplex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R]
variable (C : CochainComplex (ModuleCat R) ℤ) (A : ModuleCat R)

abbrev targetSingle := (CochainComplex.singleFunctor (ModuleCat R) 0).obj A

/-- The ordinary Hom window, with precomposition differentials. -/
def homSingleSc : ShortComplex (ModuleCat R) :=
  ShortComplex.mk
    (ModuleCat.ofHom (CategoryTheory.Linear.leftComp R A (C.d 0 1)))
    (ModuleCat.ofHom (CategoryTheory.Linear.leftComp R A (C.d (-1) 0))) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro f
      change C.d (-1) 0 ≫ C.d 0 1 ≫ f = 0
      simp)

def homSingleCycle (f : LinearMap.ker (homSingleSc C A).g.hom) :
    Cocycle C (targetSingle A) 0 :=
  Cocycle.toSingleMk f.val (by omega : (0 : ℤ) + 0 = 0) (-1) (by omega) f.property

/-- Map an ordinary Hom cocycle to its actual homotopy class. -/
def cyclesToHomSingle : LinearMap.ker (homSingleSc C A).g.hom →ₗ[R]
    ((homotopyQuotient R).obj C ⟶ (homotopyQuotient R).obj (targetSingle A)) where
  toFun f := (homotopyQuotient R).map (Cocycle.homOf (homSingleCycle C A f))
  map_add' f g := by
    rw [← Functor.map_add]
    congr 1
    change (Cocycle.equivHom _ _).symm (homSingleCycle C A (f + g)) =
      (Cocycle.equivHom _ _).symm (homSingleCycle C A f) +
        (Cocycle.equivHom _ _).symm (homSingleCycle C A g)
    rw [← map_add]
    congr 1
    exact Cocycle.toSingleMk_add f.val g.val (by omega : (0 : ℤ) + 0 = 0)
      (-1) (by omega) f.property g.property
  map_smul' r f := by
    rw [← Functor.map_smul]
    congr 1
    apply HomologicalComplex.Hom.ext
    funext n
    have hc : Cochain.toSingleMk (r • f.val) (by omega : (0 : ℤ) + 0 = 0) =
        r • Cochain.toSingleMk f.val (by omega : (0 : ℤ) + 0 = 0) := by
      apply (Cochain.toSingleEquiv (by omega : (0 : ℤ) + 0 = 0)).injective
      simp [Cochain.toSingleEquiv, Cochain.smul_v]
    exact congrArg (fun z => z.v n n (add_zero n)) hc

theorem cyclesToHomSingle_surjective : Function.Surjective (cyclesToHomSingle C A) := by
  intro α
  obtain ⟨f, rfl⟩ := (homotopyQuotient R).map_surjective α
  obtain ⟨g, hg, he⟩ := Cocycle.toSingleMk_surjective (Cocycle.ofHom f)
    0 (by omega) (-1) (by omega)
  refine ⟨⟨g, hg⟩, ?_⟩
  change (homotopyQuotient R).map (Cocycle.homOf _) = _
  rw [show homSingleCycle C A ⟨g, hg⟩ = Cocycle.ofHom f from he]
  simp

theorem quotient_homOf_eq_zero_iff (z : Cocycle C (targetSingle A) 0) :
    (homotopyQuotient R).map (Cocycle.homOf z) = 0 ↔
      z ∈ coboundaries C (targetSingle A) 0 := by
  rw [HomotopyCategory.quotient_map_eq_zero_iff, mem_coboundaries_iff z (-1) (by omega)]
  constructor
  · rintro ⟨h⟩
    obtain ⟨β, hβ⟩ := Cochain.equivHomotopy _ _ h
    exact ⟨β, by simpa using hβ.symm⟩
  · rintro ⟨β, hβ⟩
    exact ⟨(Cochain.equivHomotopy _ _).symm ⟨β, by simpa using hβ.symm⟩⟩

theorem cyclesToHomSingle_ker : LinearMap.ker (cyclesToHomSingle C A) =
    LinearMap.range (homSingleSc C A).moduleCatToCycles := by
  ext f
  change (homotopyQuotient R).map (Cocycle.homOf (homSingleCycle C A f)) = 0 ↔ _
  rw [quotient_homOf_eq_zero_iff]
  change Cocycle.toSingleMk f.val _ (-1) _ f.property ∈ coboundaries _ _ _ ↔ _
  rw [Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ 1 (by omega)]
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g, Subtype.ext hg⟩
  · rintro ⟨g, hg⟩
    exact ⟨g, congrArg Subtype.val hg⟩

/-- Genuine native homology of the Hom window equals genuine homotopy
classes into the degree-zero single complex. -/
def homSingleHomologyEquiv : (homSingleSc C A).homology ≃ₗ[R]
    ((homotopyQuotient R).obj C ⟶ (homotopyQuotient R).obj (targetSingle A)) :=
  (homSingleSc C A).moduleCatHomologyIso.toLinearEquiv.trans
    ((Submodule.quotEquivOfEq _ _ (cyclesToHomSingle_ker C A).symm).trans
      ((cyclesToHomSingle C A).quotKerEquivOfSurjective (cyclesToHomSingle_surjective C A)))

end
end Decoupling.HighDim.Torus
