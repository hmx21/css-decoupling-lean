import Decoupling.HighDim.AlgorithmTwoPipelineBackendData
import Decoupling.HighDim.AlgorithmTwoOriginalArraysSize

/-!
# Original adjacent input as finite backend data

The rank vector stores exactly the original degree-window ranks.
Outside that window the original ranks are proved zero. Coefficient
arrays are transported only along equal natural-number dimensions;
no coefficient is changed and no basis is selected.
-/
namespace Decoupling.HighDim.AlgorithmTwoBackendOriginal
open LaurentArithmetic AlgorithmTwoPipelineBackend AlgorithmTwoPipeline
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} {D h m n m' n' : ℕ}

def castDense (hm : m=m') (hn : n=n') (A : DenseMatrix K D m n h) :
    DenseMatrix K D m' n' h := by
  subst m'
  subst n'
  exact A

theorem castDense_heq (hm : m=m') (hn : n=n') (A : DenseMatrix K D m n h) :
    HEq (castDense hm hn A) A := by
  subst m'
  subst n'
  rfl

variable [Field K] {L : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]

def storedRanks : Vector ℕ (inputLength L) :=
  Vector.ofFn fun i => coords.rank (-(L:ℤ)+i)

theorem storedRanks_rankAt (j : ℤ) :
    rankAt (storedRanks (L := L) coords) j = coords.rank j := by
  by_cases hj : -(L:ℤ) ≤ j ∧ j ≤ L
  · rw [rankAt,dite_eq_left hj]
    change (Vector.ofFn (fun i : Fin (inputLength L) => coords.rank (-(L:ℤ)+i)))[
      (AlgorithmTwoPipelineBackend.slot L j hj).val] = _
    rw [Vector.getElem_ofFn]
    exact congrArg coords.rank (AlgorithmTwoPipelineBackend.slot_degree L j hj)
  · rw [rankAt,dite_eq_right hj]
    symm
    apply outside_zero (L := L) coords j
    dsimp [inputLength]
    omega

def rawInput (inp : AlgorithmTwoOriginalArrays.Input (D := D) (L := L) (h := h) coords) :
    RawInput K D L h where
  ranks := storedRanks coords
  differential i := castDense
    (storedRanks_rankAt coords (-(L:ℤ)+i+1)).symm
    (storedRanks_rankAt coords (-(L:ℤ)+i)).symm (inp.differential i)

theorem rawInput_rankAt (inp : AlgorithmTwoOriginalArrays.Input (D := D) (L := L) (h := h) coords)
    (j : ℤ) : rankAt (rawInput coords inp).ranks j = coords.rank j :=
  storedRanks_rankAt coords j

theorem rawInput_differential_heq
    (inp : AlgorithmTwoOriginalArrays.Input (D := D) (L := L) (h := h) coords)
    (i : Fin (inputLength L)) :
    HEq ((rawInput coords inp).differential i) (inp.differential i) :=
  castDense_heq _ _ _

end Decoupling.HighDim.AlgorithmTwoBackendOriginal
