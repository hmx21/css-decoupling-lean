import Decoupling.HighDim.AlgorithmTwoPhysicalTransportRealization

/-!
# HD014 executable removal of zero-weight SUM layers

Only zero-weight SUM layers are removed. SWAP layers and their physical
species labels are retained. This pure function specifies the output;
SparseCircuitProgram implements it with recorded zero tests. All matrix
and stabilizer semantics are proved for the actual filtered list.
-/
namespace Decoupling.HighDim.SparseCircuit
open Circuit Matrix PhysicalIsomorphism
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [CommRing K] [DecidableEq K] {D : ℕ} {ι : Type*}

def keep : Layer K D ι → Bool
  | .sum g => decide (g.weight ≠ 0)
  | .swap _ => true

def eraseZeroSUM (word : List (Layer K D ι)) : List (Layer K D ι) := word.filter keep

def isSwap : Layer K D ι → Bool
  | .sum _ => false
  | .swap _ => true

def swapCount (word : List (Layer K D ι)) : ℕ := word.countP isSwap

@[simp] theorem erase_nil : eraseZeroSUM ([] : List (Layer K D ι)) = [] := rfl
@[simp] theorem erase_append (a b : List (Layer K D ι)) :
    eraseZeroSUM (a ++ b) = eraseZeroSUM a ++ eraseZeroSUM b := List.filter_append _ _

theorem length_le (word : List (Layer K D ι)) : (eraseZeroSUM word).length ≤ word.length :=
  List.length_filter_le _ _

theorem mem_of_mem {word : List (Layer K D ι)} {g : Layer K D ι}
    (hg : g ∈ eraseZeroSUM word) : g ∈ word := (List.mem_filter.mp hg).1

theorem swapCount_erase (word : List (Layer K D ι)) :
    swapCount (eraseZeroSUM word) = swapCount word := by
  induction word with
  | nil => rfl
  | cons g word ih =>
    cases g with
    | sum g =>
      by_cases hz : g.weight = 0 <;>
        simp [eraseZeroSUM,keep,swapCount,isSwap,hz] at ih ⊢ <;> exact ih
    | swap g => simpa [eraseZeroSUM,keep,swapCount,isSwap] using congrArg Nat.succ ih

variable [Fintype ι] [DecidableEq ι]

omit [DecidableEq K] [Fintype ι] in
theorem zero_xMatrix (g : SUM K D ι) (hz : g.weight = 0) : g.xMatrix = 1 := by
  simp [SUM.xMatrix,hz]

omit [DecidableEq K] [Fintype ι] in
theorem zero_zMatrix (g : SUM K D ι) (hz : g.weight = 0) : g.zMatrix = 1 := by
  simp [SUM.zMatrix_formula,hz]

@[simp] theorem wordX_erase (word : List (Layer K D ι)) :
    wordX (eraseZeroSUM word) = wordX word := by
  induction word with
  | nil => rfl
  | cons g word ih =>
    simp only [eraseZeroSUM] at ih
    cases g with
    | sum g =>
      by_cases hz : g.weight = 0 <;>
        simp [eraseZeroSUM,keep,hz,wordX_cons,Layer.xMatrix,zero_xMatrix,ih]
    | swap g => simp [eraseZeroSUM,keep,wordX_cons,ih]

@[simp] theorem wordZ_erase (word : List (Layer K D ι)) :
    wordZ (eraseZeroSUM word) = wordZ word := by
  induction word with
  | nil => rfl
  | cons g word ih =>
    simp only [eraseZeroSUM] at ih
    cases g with
    | sum g =>
      by_cases hz : g.weight = 0 <;>
        simp [eraseZeroSUM,keep,hz,wordZ_cons,Layer.zMatrix,zero_zMatrix,ih]
    | swap g => simp [eraseZeroSUM,keep,wordZ_cons,ih]

omit [Fintype ι] in
theorem localCircuit_erase (word : List (Layer K D ι)) : LocalCircuit (eraseZeroSUM word) :=
  localCircuit _

variable {Q C C' Z Z' : Type*}
  [Fintype Q] [Fintype C] [Fintype C'] [Fintype Z] [Fintype Z'] [DecidableEq Q]

omit [Fintype Q] [DecidableEq Q] in
theorem transports_erase (word : List (Layer K D ι)) (e : Q ≃ ι)
    (HC : Matrix C Q (Laurent K D)) (HT : Matrix C' ι (Laurent K D))
    (BC : Matrix Q Z (Laurent K D)) (BT : Matrix ι Z' (Laurent K D))
    (h : Transports word e HC HT BC BT) : Transports (eraseZeroSUM word) e HC HT BC BT := by
  simpa only [Transports,wordZ_erase,wordX_erase] using h

end Decoupling.HighDim.SparseCircuit
