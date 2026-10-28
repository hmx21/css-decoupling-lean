import Decoupling.HighDim.AlgorithmTwoFiniteComplexSliceMap
import Decoupling.HighDim.StableFreeEffectiveDense

/-!
# Pure actual-degree slices in the common original coordinate window

The degree slot and within-slot indices are explicit integer arithmetic.
All casts are along proved degree equalities, and all runtime data are
coefficient lookups in the original stored arrays.
-/
namespace Decoupling.HighDim.StableFree.Effective.CochainProgram
open Matrix LaurentArithmetic AlgorithmTwoFiniteComplex
variable {K : Type*} [Field K] {D h : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def degreeSlot (L : ℕ) (j : ℤ) (hj : -(L:ℤ) ≤ j ∧ j ≤ L) : Fin (2*L+1) :=
  ⟨(j+L).toNat,by omega⟩

theorem degreeSlot_degree (L : ℕ) (j : ℤ) (hj : -(L:ℤ) ≤ j ∧ j ≤ L) :
    -(L:ℤ)+(degreeSlot L j hj : ℕ) = j := by
  dsimp [degreeSlot]
  omega

/-- Original-degree slice with only proof-erased dimension casts. -/
def sliceAt (rC rT : ℤ → ℕ) (loC loT : ℤ) (lengthC lengthT : ℕ)
    (row : Fin lengthC) (col : Fin lengthT) (b a : ℤ)
    (hb : loC+row=b) (ha : loT+col=a)
    (A : DenseMatrix K D (totalRank rC loC lengthC) (totalRank rT loT lengthT) h) :
    DenseMatrix K D (rC b) (rT a) h := by
  subst b
  subst a
  exact sliceMap A (slotSelector (fun i : Fin lengthC => rC (loC+i)) row)
    (slotSelector (fun i : Fin lengthT => rT (loT+i)) col)

def boundedSlice (rC rT : ℤ → ℕ) (L : ℕ) (b a : ℤ)
    (hb : -(L:ℤ) ≤ b ∧ b ≤ L) (ha : -(L:ℤ) ≤ a ∧ a ≤ L)
    (A : DenseMatrix K D (totalRank rC (-(L:ℤ)) (2*L+1))
      (totalRank rT (-(L:ℤ)) (2*L+1)) h) : DenseMatrix K D (rC b) (rT a) h :=
  sliceAt rC rT (-(L:ℤ)) (-(L:ℤ)) (2*L+1) (2*L+1)
    (degreeSlot L b hb) (degreeSlot L a ha) b a
    (degreeSlot_degree L b hb) (degreeSlot_degree L a ha) A

noncomputable section
variable {C T : CochainComplex (ModuleCat (Laurent K D)) ℤ}

theorem sliceAt_native (cC : StableFree.Coordinates C) (cT : StableFree.Coordinates T)
    (loC loT : ℤ) (lengthC lengthT : ℕ)
    (outC : ∀ j, j < loC ∨ loC+lengthC ≤ j → cC.rank j = 0)
    (outT : ∀ j, j < loT ∨ loT+lengthT ≤ j → cT.rank j = 0)
    (row : Fin lengthC) (col : Fin lengthT) (b a : ℤ)
    (hb : loC+row=b) (ha : loT+col=a)
    (A : DenseMatrix K D (totalRank cC.rank loC lengthC) (totalRank cT.rank loT lengthT) h)
    (f : T.X a →ₗ[Laurent K D] C.X b)
    (hA : ∀ x, matrixDenote A *ᵥ (AlgorithmTwoFiniteComplex.Coordinates.ofBounded cT loT lengthT outT).embed a x =
      (AlgorithmTwoFiniteComplex.Coordinates.ofBounded cC loC lengthC outC).embed b (f x)) :
    matrixDenote (sliceAt cC.rank cT.rank loC loT lengthC lengthT row col b a hb ha A) =
      LinearMap.toMatrix' ((cC.equiv b).toLinearMap.comp (f.comp (cT.equiv a).symm.toLinearMap)) := by
  subst b
  subst a
  apply Matrix.mulVec_injective
  funext x
  obtain ⟨x,rfl⟩ := (cT.equiv (loT+col)).surjective x
  rw [LinearMap.toMatrix'_mulVec]
  change matrixDenote (sliceMap A
    (slotSelector (fun i : Fin lengthC => cC.rank (loC+i)) row)
    (slotSelector (fun i : Fin lengthT => cT.rank (loT+i)) col)) *ᵥ cT.equiv (loT+col) x =
      cC.equiv (loC+row) (f ((cT.equiv (loT+col)).symm (cT.equiv (loT+col) x)))
  rw [LinearEquiv.symm_apply_apply]
  exact sliceMap_between cT cC loT loC lengthT lengthC outT outC row col A f hA x

theorem boundedSlice_native (cC : StableFree.Coordinates C) (cT : StableFree.Coordinates T)
    (L : ℕ)
    (outC : ∀ j, j < -(L:ℤ) ∨ -(L:ℤ)+(2*L+1:ℕ) ≤ j → cC.rank j = 0)
    (outT : ∀ j, j < -(L:ℤ) ∨ -(L:ℤ)+(2*L+1:ℕ) ≤ j → cT.rank j = 0)
    (b a : ℤ) (hb : -(L:ℤ) ≤ b ∧ b ≤ L) (ha : -(L:ℤ) ≤ a ∧ a ≤ L)
    (A : DenseMatrix K D (totalRank cC.rank (-(L:ℤ)) (2*L+1))
      (totalRank cT.rank (-(L:ℤ)) (2*L+1)) h)
    (f : T.X a →ₗ[Laurent K D] C.X b)
    (hA : ∀ x, matrixDenote A *ᵥ (AlgorithmTwoFiniteComplex.Coordinates.ofBounded cT _ _ outT).embed a x =
      (AlgorithmTwoFiniteComplex.Coordinates.ofBounded cC _ _ outC).embed b (f x)) :
    matrixDenote (boundedSlice cC.rank cT.rank L b a hb ha A) =
      LinearMap.toMatrix' ((cC.equiv b).toLinearMap.comp (f.comp (cT.equiv a).symm.toLinearMap)) :=
  sliceAt_native cC cT _ _ _ _ outC outT _ _ _ _ _ _ A f hA

end
end Decoupling.HighDim.StableFree.Effective.CochainProgram
