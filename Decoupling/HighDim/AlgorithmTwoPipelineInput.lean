import Decoupling.HighDim.AlgorithmTwoFiniteComplexSlice
import Decoupling.HighDim.AlgorithmTwoLinearComparisonNative
import Decoupling.HighDim.AlgorithmTwoComputedLayersProgram

/-!
# Original bounded-complex input of Algorithm 2

Only the original finite free coordinates, the actual original total
matrix, native strict bounds, and the original split-profile proof are
inputs. Per-degree windows are pure verified slices. The old formal
multiplicities occur only in a proof; output multiplicities are computed.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipeline
open CategoryTheory AlgorithmTwoFiniteComplex Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard
variable {K : Type} [Field K] {D L h : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]

abbrev inputLength (L : ℕ) := 2*L+1
abbrev inputRank (cC : StableFree.Coordinates C) (L : ℕ) := totalRank cC.rank (-(L:ℤ)) (inputLength L)

theorem outside_zero (j : ℤ) (hj : j < -(L:ℤ) ∨ -(L:ℤ)+inputLength L ≤ j) : cC.rank j = 0 := by
  apply AlgorithmTwoFiniteComplex.rank_zero_of_isZero cC j
  rcases hj with hj | hj
  · exact C.isZero_of_isStrictlyGE (-(L:ℤ)) j hj
  · exact C.isZero_of_isStrictlyLE (L:ℤ) j (by dsimp only [inputLength] at hj; omega)

noncomputable def inputCoordinates : Coordinates C (inputRank cC L) :=
  Coordinates.ofBounded cC (-(L:ℤ)) (inputLength L) (outside_zero cC)

structure Input where
  differential : LaurentArithmetic.DenseMatrix K D (inputRank cC L) (inputRank cC L) h
  represents : (inputCoordinates cC).RepresentsDifferential (LaurentArithmetic.matrixDenote differential)
  formal : ∃ old : Fin (D-1) → ℕ,
    Nonempty (DerivedCategory.Q.obj (Toric.stackModel K D (Toric.copyForms D old)) ≅ DerivedCategory.Q.obj C)

def slot (L z : ℕ) (hz : z ≤ L) : Fin (inputLength L) := ⟨L+z, by dsimp [inputLength]; omega⟩

theorem slot_degree (L z : ℕ) (hz : z ≤ L) : -(L:ℤ)+(slot L z hz : ℤ) = z := by
  dsimp [slot]
  omega

variable (inp : Input (D := D) (L := L) (h := h) cC) (hDL : D ≤ L)

def sliceAt (a b : ℤ) (row col : Fin (inputLength L))
    (ha : -(L:ℤ)+(col:ℤ)=a) (hb : -(L:ℤ)+(row:ℤ)=b) :
    LaurentArithmetic.DenseMatrix K D (cC.rank b) (cC.rank a) h := by
  subst a
  subst b
  exact sliceBlock inp.differential row col

theorem sliceAt_action (a b : ℤ) (row col : Fin (inputLength L))
    (ha : -(L:ℤ)+(col:ℤ)=a) (hb : -(L:ℤ)+(row:ℤ)=b) (hn : b=a+1) :
    ∀ x : C.X a, LaurentArithmetic.matrixDenote (sliceAt cC inp a b row col ha hb) *ᵥ cC.equiv a x =
      cC.equiv b ((C.d a b).hom x) := by
  subst a
  subst b
  exact sliceBlock_differential cC (-(L:ℤ)) (inputLength L) (outside_zero cC)
    inp.differential inp.represents row col hn

def incoming (j : Fin (D-1)) : LaurentArithmetic.DenseMatrix K D
    (cC.rank (j.val+1)) (cC.rank ((j.val:ℤ)+1-1)) h :=
  sliceAt cC inp ((j.val:ℤ)+1-1) (j.val+1)
    (slot L (j.val+1) (by omega)) (slot L j.val (by omega))
    (by rw [slot_degree]; omega) (by rw [slot_degree]; push_cast; rfl)

def outgoing (j : Fin (D-1)) : LaurentArithmetic.DenseMatrix K D
    (cC.rank ((j.val:ℤ)+1+1)) (cC.rank (j.val+1)) h :=
  sliceAt cC inp (j.val+1) ((j.val:ℤ)+1+1)
    (slot L (j.val+2) (by omega)) (slot L (j.val+1) (by omega))
    (by rw [slot_degree]; push_cast; rfl) (by rw [slot_degree]; push_cast; omega)

theorem incoming_action (j : Fin (D-1)) : ∀ x : C.X ((j.val:ℤ)+1-1),
    LaurentArithmetic.matrixDenote (incoming cC inp hDL j) *ᵥ cC.equiv ((j.val:ℤ)+1-1) x =
      cC.equiv (j.val+1) ((C.d ((j.val:ℤ)+1-1) (j.val+1)).hom x) := by
  exact sliceAt_action cC inp _ _ _ _ _ _ (by omega)

theorem outgoing_action (j : Fin (D-1)) : ∀ x : C.X (j.val+1),
    LaurentArithmetic.matrixDenote (outgoing cC inp hDL j) *ᵥ cC.equiv (j.val+1) x =
      cC.equiv ((j.val:ℤ)+1+1) ((C.d (j.val+1) ((j.val:ℤ)+1+1)).hom x) := by
  exact sliceAt_action cC inp _ _ _ _ _ _ (by omega)

end Decoupling.HighDim.AlgorithmTwoPipeline
