import Decoupling.HighDim.AlgorithmTwoFiniteComplexCone
import Decoupling.HighDim.AlgorithmTwoToricDataConeCoordinates

/-! # Exact total differential of the actual native mapping cone -/
namespace Decoupling.HighDim.AlgorithmTwoFiniteComplex
open CategoryTheory Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
variable {R : Type} [CommRing R] {m n : ℕ}
variable {T C : CochainComplex (ModuleCat R) ℤ}

def coneMatrix (dT : Matrix (Fin m) (Fin m) R) (dC : Matrix (Fin n) (Fin n) R)
    (A : Matrix (Fin n) (Fin m) R) : Matrix (Fin (m+n)) (Fin (m+n)) R :=
  (Matrix.fromBlocks (-dT) 0 A dC).submatrix finSumFinEquiv.symm finSumFinEquiv.symm

theorem coneMatrix_mul_join (dT : Matrix (Fin m) (Fin m) R) (dC : Matrix (Fin n) (Fin n) R)
    (A : Matrix (Fin n) (Fin m) R) (x : Fin m → R) (y : Fin n → R) :
    coneMatrix dT dC A *ᵥ joinCoordinates (x,y) =
      joinCoordinates (-(dT *ᵥ x), A *ᵥ x + dC *ᵥ y) := by
  have he : joinCoordinates (x,y) ∘ finSumFinEquiv = Sum.elim x y := by
    funext i
    cases i with
    | inl a => exact joinCoordinates_inl x y a
    | inr b => exact joinCoordinates_inr x y b
  rw [coneMatrix, Matrix.submatrix_mulVec_equiv, Equiv.symm_symm, he, Matrix.fromBlocks_mulVec]
  simp only [Function.comp_def, Sum.elim_inl, Sum.elim_inr, Matrix.zero_mulVec, add_zero,
    Matrix.neg_mulVec]
  rfl

theorem coneMatrix_represents (f : T ⟶ C) (cT : Coordinates T m) (cC : Coordinates C n)
    (dT : Matrix (Fin m) (Fin m) R) (dC : Matrix (Fin n) (Fin n) R)
    (A : Matrix (Fin n) (Fin m) R)
    (hdT : cT.RepresentsDifferential dT) (hdC : cC.RepresentsDifferential dC)
    (hA : ∀ j x, A *ᵥ cT.embed j x = cC.embed j ((f.f j).hom x)) :
    (Coordinates.cone f cT cC).RepresentsDifferential (coneMatrix dT dC A) := by
  intro j x
  change coneMatrix dT dC A *ᵥ joinCoordinates
    (cT.embed (j+1) (((AlgorithmTwoComparison.actualConeTermIso f j).hom x).1),
     cC.embed j (((AlgorithmTwoComparison.actualConeTermIso f j).hom x).2)) =
    joinCoordinates
    (cT.embed (j+1+1) (((AlgorithmTwoComparison.actualConeTermIso f (j+1)).hom
      ((CochainComplex.mappingCone f).d j (j+1) x)).1),
     cC.embed (j+1) (((AlgorithmTwoComparison.actualConeTermIso f (j+1)).hom
      ((CochainComplex.mappingCone f).d j (j+1) x)).2))
  rw [coneMatrix_mul_join, AlgorithmTwoToricData.coneCoordinate_d,
    hdT, hdC, hA, map_neg, map_add]

theorem cochainMap_represents (cT : Coordinates T m) (cC : Coordinates C n)
    (dT : Matrix (Fin m) (Fin m) R) (dC : Matrix (Fin n) (Fin n) R)
    (hdT : cT.RepresentsDifferential dT) (hdC : cC.RepresentsDifferential dC)
    (A : Matrix (Fin n) (Fin m) R) (hA : Homogeneous cT.degree cC.degree 0 A)
    (hcomm : dC*A=A*dT) (j : ℤ) (x : T.X j) :
    A *ᵥ cT.embed j x = cC.embed j
      (((cochainMap cT cC dT dC hdT hdC A hA hcomm).f j).hom x) :=
  (component_embed_zero cT cC A j hA x).symm

end
end Decoupling.HighDim.AlgorithmTwoFiniteComplex
