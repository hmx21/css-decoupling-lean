import Decoupling.HighDim.SparseCircuit

/-! # Zero SUMs are literally identity local complex unitaries -/
namespace Decoupling.HighDim.SparseCircuit
open Circuit PauliUnitary
set_option backward.isDefEq.respectTransparency false
variable {p D : ℕ} [NeZero p] {ι : Type*}

omit [NeZero p] in
theorem zero_localAction (g : SUM (ZMod p) D ι) (hz : g.weight = 0) (a b : ZMod p) :
    g.localAction a b = (a,b) := by simp [SUM.localAction,hz]

theorem zero_localUnitary (g : SUM (ZMod p) D ι) (hz : g.weight = 0) :
    (layerLocalUnitary (.sum g) : Matrix (Config p Bool) (Config p Bool) ℂ) = 1 := by
  have he : sumGate false true g.weight Bool.false_ne_true =
      LinearEquiv.refl (ZMod p) (Config p Bool) := by
    ext x i
    simp [sumGate_apply,sumMatrix,hz]
  change permutation (sumGate false true g.weight Bool.false_ne_true).toEquiv = 1
  rw [he]
  change Equiv.Perm.permMatrix ℂ (Equiv.refl (Config p Bool)) = 1
  exact Matrix.permMatrix_refl

variable {K : Type*} [CommRing K] [DecidableEq K] [DecidableEq ι]

theorem wordXConfig_erase (word : List (Layer K D ι)) (v : ι → Translation D → K) :
    wordXConfig (eraseZeroSUM word) v = wordXConfig word v := by
  induction word with
  | nil => rfl
  | cons g word ih =>
    simp only [eraseZeroSUM] at ih
    cases g with
    | sum g =>
      by_cases hz : g.weight = 0 <;> funext i cell <;>
        simp [eraseZeroSUM,keep,hz,wordXConfig,Layer.xConfig,SUM.xConfig,ih]
    | swap g => simp [eraseZeroSUM,keep,wordXConfig,ih]

theorem wordZConfig_erase (word : List (Layer K D ι)) (v : ι → Translation D → K) :
    wordZConfig (eraseZeroSUM word) v = wordZConfig word v := by
  induction word with
  | nil => rfl
  | cons g word ih =>
    simp only [eraseZeroSUM] at ih
    cases g with
    | sum g =>
      by_cases hz : g.weight = 0 <;> funext i cell <;>
        simp [eraseZeroSUM,keep,hz,wordZConfig,Layer.zConfig,SUM.zConfig,ih]
    | swap g => simp [eraseZeroSUM,keep,wordZConfig,ih]

end Decoupling.HighDim.SparseCircuit
