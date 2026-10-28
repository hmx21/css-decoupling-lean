import Decoupling.HighDim.AlgorithmTwoPipelineRadius
import Decoupling.HighDim.AlgorithmTwoPipelineSelectors
import Decoupling.HighDim.AlgorithmTwoToricData

/-! # Pure placement of the stored computed cocycles into the actual comparison target -/
namespace Decoupling.HighDim.AlgorithmTwoPipeline
open CategoryTheory Matrix AlgorithmTwoFiniteComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
variable (inp : Input (D := D) (L := L) (h := h) cC) (hDL : D ≤ L)

abbrev InputLayers := StoredLayers cC (incoming cC inp hDL) (outgoing cC inp hDL)

private theorem stored_dimension (s : InputLayers cC inp hDL) (j : Fin (D-1)) :
    (s.result j).dimension = AlgorithmTwoToricData.multiplicities D s.multiplicities j :=
  s.result_dimension j

def localCocycleColumn (s : InputLayers cC inp hDL)
    (i : AlgorithmTwoToricData.Copy D s.multiplicities) :
    Vector (LaurentArithmetic.Dense K D s.commonRadius) (cC.rank (i.1.val+1)) :=
  Vector.ofFn fun a => LaurentArithmetic.pad
    (s.result i.1).cocycles[a][Fin.cast (stored_dimension cC inp hDL s i.1).symm i.2] s.commonRadius

noncomputable def nativeStoredCycle (s : InputLayers cC inp hDL)
    (i : AlgorithmTwoToricData.Copy D s.multiplicities) : C.X (i.1.val+1) :=
  (cC.equiv (i.1.val+1)).symm (fun a => LaurentArithmetic.denote
    (s.result i.1).cocycles[a][Fin.cast (stored_dimension cC inp hDL s i.1).symm i.2])

def columnAt (j : ℤ) (i : Fin (inputLength L)) (hi : -(L:ℤ)+(i:ℤ)=j)
    {B : ℕ} (v : Vector (LaurentArithmetic.Dense K D B) (cC.rank j)) :
    SlotColumn K D B (fun i : Fin (inputLength L) => cC.rank (-(L:ℤ)+(i:ℤ))) := by
  subst j
  exact ⟨i,v⟩

noncomputable section

omit [DecidableEq K] in
theorem columnAt_native (j : ℤ) (i : Fin (inputLength L)) (hi : -(L:ℤ)+(i:ℤ)=j)
    {B : ℕ} (v : Vector (LaurentArithmetic.Dense K D B) (cC.rank j)) :
    (fun a => LaurentArithmetic.denote (placeColumn (columnAt cC j i hi v))[a]) =
      (inputCoordinates (L := L) cC).embed j ((cC.equiv j).symm (fun a => LaurentArithmetic.denote v[a])) := by
  subst j
  exact placeColumn_native cC (-(L:ℤ)) (inputLength L) (outside_zero (L := L) cC) ⟨i,v⟩

end

def cocycleColumns (s : InputLayers cC inp hDL) :
    Vector (SlotColumn K D s.commonRadius (fun i : Fin (inputLength L) => cC.rank (-(L:ℤ)+(i:ℤ))))
      (AlgorithmTwoToricData.copyCount D s.multiplicities) :=
  Vector.ofFn fun a =>
    let i := AlgorithmTwoToricData.copyEquiv D s.multiplicities a
    columnAt cC (i.1.val+1) (slot L (i.1.val+1) (by have hj := i.1.isLt; omega))
      (by rw [slot_degree]; push_cast; rfl) (localCocycleColumn cC inp hDL s i)

def targetCocycles (s : InputLayers cC inp hDL) :
    LaurentArithmetic.DenseMatrix K D (inputRank cC L)
      (AlgorithmTwoToricData.copyCount D s.multiplicities) s.commonRadius :=
  placeColumns (cocycleColumns cC inp hDL s)

noncomputable section

theorem localCocycleColumn_correct (s : InputLayers cC inp hDL)
    (i : AlgorithmTwoToricData.Copy D s.multiplicities) :
    (fun a => LaurentArithmetic.denote (localCocycleColumn cC inp hDL s i)[a]) =
      cC.equiv (i.1.val+1) (nativeStoredCycle cC inp hDL s i) := by
  rw [nativeStoredCycle,LinearEquiv.apply_symm_apply]
  funext a
  simp only [localCocycleColumn, Fin.getElem_fin, Vector.getElem_ofFn]
  exact LaurentArithmetic.pad_correct _ (s.radius_le_commonRadius i.1)

theorem targetCocycles_native (s : InputLayers cC inp hDL)
    (a : Fin (AlgorithmTwoToricData.copyCount D s.multiplicities)) :
    (LaurentArithmetic.matrixDenote (targetCocycles cC inp hDL s)).col a =
      (inputCoordinates (L := L) cC).embed
        (((AlgorithmTwoToricData.copyEquiv D s.multiplicities a).1.val:ℤ)+1)
        (nativeStoredCycle cC inp hDL s (AlgorithmTwoToricData.copyEquiv D s.multiplicities a)) := by
  change (fun r => LaurentArithmetic.denote ((placeColumns (cocycleColumns cC inp hDL s))[r][a])) = _
  simp only [placeColumns,cocycleColumns,Fin.getElem_fin,Vector.getElem_ofFn,Fin.eta]
  let i := AlgorithmTwoToricData.copyEquiv D s.multiplicities a
  have hp := columnAt_native (L := L) cC (i.1.val+1)
    (slot L (i.1.val+1) (by have hj := i.1.isLt; omega))
    (by rw [slot_degree]; push_cast; rfl) (localCocycleColumn cC inp hDL s i)
  rw [localCocycleColumn_correct cC inp hDL s i,LinearEquiv.symm_apply_apply] at hp
  exact hp

end
end Decoupling.HighDim.AlgorithmTwoPipeline
