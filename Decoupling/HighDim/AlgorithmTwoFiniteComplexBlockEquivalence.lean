import Decoupling.HighDim.AlgorithmTwoFiniteComplexConeBlocks
import Decoupling.HighDim.AlgorithmTwoFiniteComplexHomotopy

/-! # Native homotopy equivalence from the actual solved cone blocks -/
namespace Decoupling.HighDim.AlgorithmTwoFiniteComplex
open CategoryTheory HomologicalComplex Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
variable {R : Type} [CommRing R] {m n : ℕ}
variable {T C : CochainComplex (ModuleCat R) ℤ}

variable (cT : Coordinates T m) (cC : Coordinates C n)
  (dT : Matrix (Fin m) (Fin m) R) (dC : Matrix (Fin n) (Fin n) R)
  (hdT : cT.RepresentsDifferential dT) (hdC : cC.RepresentsDifferential dC)
  (f : T ⟶ C) (A : Matrix (Fin n) (Fin m) R)
  (hA : ∀ j x, A *ᵥ cT.embed j x = cC.embed j ((f.f j).hom x))
  (H : Matrix (Fin (m+n)) (Fin (m+n)) R)
  (hH : Homogeneous (coneDegree cT.degree cC.degree) (coneDegree cT.degree cC.degree) (-1) H)
  (he : coneMatrix dT dC A * H + H * coneMatrix dT dC A = 1)

include hH he in
def blockInverse : C ⟶ T :=
  cochainMap cC cT dC dT hdC hdT (inverseBlock H)
    (inverseBlock_homogeneous _ _ _ hH) (cone_blocks dT dC A H he).1

theorem blockInverse_represents (j : ℤ) (x : C.X j) :
    inverseBlock H *ᵥ cC.embed j x =
      cT.embed j (((blockInverse cT cC dT dC hdT hdC A H hH he).f j).hom x) :=
  cochainMap_represents cC cT dC dT hdC hdT _ (inverseBlock_homogeneous _ _ _ hH)
    (cone_blocks dT dC A H he).1 j x

def blockHomotopyEquiv : HomotopyEquiv T C where
  hom := f
  inv := blockInverse cT cC dT dC hdT hdC A H hH he
  homotopyHomInvId := matrixHomotopy cT cT dT dT hdT hdT _ _ (inverseBlock H * A) 1 (sourceBlock H)
    (by
      intro j x
      rw [← Matrix.mulVec_mulVec, hA, blockInverse_represents cT cC dT dC hdT hdC A H hH he]
      rfl)
    (by intro j x; simp)
    (sourceBlock_homogeneous _ _ _ hH) (cone_blocks dT dC A H he).2.1
  homotopyInvHomId := matrixHomotopy cC cC dC dC hdC hdC _ _ (A * inverseBlock H) 1 (targetBlock H)
    (by
      intro j x
      rw [← Matrix.mulVec_mulVec, blockInverse_represents cT cC dT dC hdT hdC A H hH he, hA]
      rfl)
    (by intro j x; simp)
    (targetBlock_homogeneous _ _ _ hH) (cone_blocks dT dC A H he).2.2

@[simp] theorem blockHomotopyEquiv_hom : (blockHomotopyEquiv cT cC dT dC hdT hdC f A hA H hH he).hom = f := rfl

theorem blockHomotopyEquiv_inv_represents (j : ℤ) (x : C.X j) :
    inverseBlock H *ᵥ cC.embed j x = cT.embed j
      ((((blockHomotopyEquiv cT cC dT dC hdT hdC f A hA H hH he).inv).f j).hom x) :=
  blockInverse_represents cT cC dT dC hdT hdC A H hH he j x

theorem blockHomotopyEquiv_source_represents (a b : ℤ) (hab : b+1=a) (x : T.X a) :
    sourceBlock H *ᵥ cT.embed a x = cT.embed b
      ((((blockHomotopyEquiv cT cC dT dC hdT hdC f A hA H hH he).homotopyHomInvId).hom a b).hom x) := by
  dsimp only [blockHomotopyEquiv]
  erw [matrixHomotopy_hom_at (hab := hab)]
  exact (component_embed_between cT cT (sourceBlock H) (-1) a b (by omega)
    (sourceBlock_homogeneous _ _ _ hH) x).symm

theorem blockHomotopyEquiv_target_represents (a b : ℤ) (hab : b+1=a) (x : C.X a) :
    targetBlock H *ᵥ cC.embed a x = cC.embed b
      ((((blockHomotopyEquiv cT cC dT dC hdT hdC f A hA H hH he).homotopyInvHomId).hom a b).hom x) := by
  dsimp only [blockHomotopyEquiv]
  erw [matrixHomotopy_hom_at (hab := hab)]
  exact (component_embed_between cC cC (targetBlock H) (-1) a b (by omega)
    (targetBlock_homogeneous _ _ _ hH) x).symm

end
end Decoupling.HighDim.AlgorithmTwoFiniteComplex
