import Decoupling.HighDim.AlgorithmTwoPipelineInput
import Decoupling.HighDim.StableFreeEffectiveCochainFrame

/-! # Explicit original-term selector tables for the input coordinate frame -/
namespace Decoupling.HighDim.AlgorithmTwoPipeline
open CategoryTheory AlgorithmTwoFiniteComplex StableFree.Effective.CochainProgram
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] {D L : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]

def integerSlot (j : ℤ) (hj : -(L:ℤ) ≤ j ∧ j ≤ L) : Fin (inputLength L) :=
  ⟨(j+L).toNat, by dsimp only [inputLength]; omega⟩

theorem integerSlot_degree (j : ℤ) (hj : -(L:ℤ) ≤ j ∧ j ≤ L) :
    -(L:ℤ)+(integerSlot j hj : ℤ)=j := by dsimp [integerSlot]; omega

def originalSelector (j : ℤ) (a : Fin (cC.rank j)) : Fin (inputRank cC L) :=
  if hj : -(L:ℤ) ≤ j ∧ j ≤ L then
    finSigmaFinEquiv ⟨integerSlot j hj, Fin.cast (congrArg cC.rank (integerSlot_degree j hj)).symm a⟩
  else False.elim (by
    have hz := outside_zero (L := L) cC j (by dsimp [inputLength]; omega)
    have ha := a.isLt
    omega)

def originalSelectors : TermSelectors cC.rank (inputRank cC L) where
  atDegree j := Vector.ofFn (originalSelector (L := L) cC j)

private theorem bounded_rows_cast (j : ℤ) (i : Fin (inputLength L)) (hi : -(L:ℤ)+(i:ℤ)=j)
    (x : C.X j) (a : Fin (cC.rank j)) :
    (inputCoordinates (L := L) cC).embed j x
      (finSigmaFinEquiv ⟨i,Fin.cast (congrArg cC.rank hi).symm a⟩) = cC.equiv j x a := by
  subst j
  simpa [inputCoordinates] using
    bounded_embed_at cC (-(L:ℤ)) (inputLength L) (outside_zero (L := L) cC) _ x i a

private theorem bounded_columns_cast (j : ℤ) (i : Fin (inputLength L)) (hi : -(L:ℤ)+(i:ℤ)=j)
    (a : Fin (cC.rank j)) :
    (inputCoordinates (L := L) cC).embed j ((cC.equiv j).symm (Pi.single a 1)) =
      Pi.single (finSigmaFinEquiv ⟨i,Fin.cast (congrArg cC.rank hi).symm a⟩) 1 := by
  subst j
  exact bounded_embed_single cC (-(L:ℤ)) (inputLength L) (outside_zero (L := L) cC) i a

theorem originalSelectors_realizes : FrameRealizes cC (inputCoordinates (L := L) cC) (originalSelectors (L := L) cC) := by
  constructor
  · intro j x a
    change (inputCoordinates (L := L) cC).embed j x ((Vector.ofFn (originalSelector (L := L) cC j)).get a) = _
    change (inputCoordinates (L := L) cC).embed j x ((Vector.ofFn (originalSelector (L := L) cC j))[a.val]) = _
    rw [Vector.getElem_ofFn]
    unfold originalSelector
    split_ifs with hj
    · exact bounded_rows_cast cC j (integerSlot j hj) (integerSlot_degree j hj) x a
    · have hz := outside_zero (L := L) cC j (by dsimp [inputLength]; omega)
      have ha := a.isLt
      omega
  · intro j a
    change _ = Pi.single ((Vector.ofFn (originalSelector (L := L) cC j)).get a) 1
    change _ = Pi.single ((Vector.ofFn (originalSelector (L := L) cC j))[a.val]) 1
    rw [Vector.getElem_ofFn]
    unfold originalSelector
    split_ifs with hj
    · exact bounded_columns_cast cC j (integerSlot j hj) (integerSlot_degree j hj) a
    · have hz := outside_zero (L := L) cC j (by dsimp [inputLength]; omega)
      have ha := a.isLt
      omega

end Decoupling.HighDim.AlgorithmTwoPipeline
