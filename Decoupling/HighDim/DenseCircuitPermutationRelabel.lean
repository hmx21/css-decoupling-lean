import Decoupling.HighDim.DenseCircuitPermutation

/-! # Executable species relabelling of actual SUM and SWAP gate data -/
namespace Decoupling.HighDim.DenseCircuitPermutation
open Circuit Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type*} {D : ℕ} {ι κ : Type*}

def relabelSwap (e : ι ≃ κ) (g : Circuit.SWAP ι) : Circuit.SWAP κ :=
  ⟨e g.left,e g.right,fun h => g.distinct (e.injective h)⟩

def relabelLayer (e : ι ≃ κ) : Circuit.Layer K D ι → Circuit.Layer K D κ
  | .sum g => .sum (g.relabel e)
  | .swap g => .swap (relabelSwap e g)

variable [CommRing K] [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] in
theorem relabelSwap_matrix (e : ι ≃ κ) (g : Circuit.SWAP ι) :
    (relabelSwap e g).matrix (K := K) (D := D) = g.matrix.submatrix e.symm e.symm := by
  funext i j
  simp only [Circuit.SWAP.matrix, Circuit.permMatrix_apply, Matrix.submatrix_apply, relabelSwap]
  have hs : e (Equiv.swap g.left g.right (e.symm j)) = Equiv.swap (e g.left) (e g.right) j := by
    simpa only [Equiv.apply_symm_apply] using e.injective.map_swap g.left g.right (e.symm j)
  rw [← hs]
  simp only [Equiv.symm_apply_eq]

omit [Fintype ι] [Fintype κ] in
theorem relabelLayer_z (e : ι ≃ κ) (g : Circuit.Layer K D ι) :
    (relabelLayer e g).zMatrix = g.zMatrix.submatrix e.symm e.symm := by
  cases g with
  | sum g =>
    change (g.relabel e).zMatrix = g.zMatrix.submatrix e.symm e.symm
    simp [Circuit.SUM.zMatrix_formula, Circuit.SUM.relabel, Matrix.submatrix_sub]
  | swap g => exact relabelSwap_matrix e g

theorem relabel_wordZ (e : ι ≃ κ) (word : List (Circuit.Layer K D ι)) :
    Circuit.wordZ (word.map (relabelLayer e)) = (Circuit.wordZ word).submatrix e.symm e.symm := by
  induction word with
  | nil => simp
  | cons g word ih =>
    simp only [List.map_cons, Circuit.wordZ_cons, relabelLayer_z, ih, Matrix.submatrix_mul_equiv]

end Decoupling.HighDim.DenseCircuitPermutation
