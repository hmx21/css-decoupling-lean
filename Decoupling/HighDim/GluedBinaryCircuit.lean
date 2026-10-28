import Decoupling.HighDim.GluedSUMCircuit
import Mathlib.Algebra.CharP.Two

/-!
# The binary example is one parallel CNOT layer

There are two gate pairs per retained cell: edge 2 in row 0 controls
plaquette 12 in row 1; edge 3 in row 0 controls plaquette 13 in row 1.
The explicit two-family word has the required shear action, and the
union of all its pairs is disjoint, so the two families execute together.
-/

namespace Decoupling.HighDim.GluedDirectional

open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

private theorem binary_derivative_basis (r t : Fin 2) :
    rowCoordinates 2 (laurentDerivative (ZMod 2) 1 (monomial (ZMod 2) (row 2 t))) r =
      if r = 0 ∧ t = 1 then 1 else 0 := by
  have hone : rowCoordinates 2 (1 : Laurent (ZMod 2) 3) = Pi.single 0 1 := by
    simpa [row] using rowCoordinates_basis 2 0
  fin_cases t <;> fin_cases r <;> simp [row, translationBasis, hone]

theorem binary_quditN : operatorMatrix 2 (quditN 2) =
    Matrix.single (1, 0) (3, 1) 1 + Matrix.single (2, 0) (4, 1) 1 := by
  apply Matrix.ext
  rintro ⟨i, r⟩ ⟨j, t⟩
  rw [quditN_entry, binary_derivative_basis]
  fin_cases i <;> fin_cases j <;> fin_cases r <;> fin_cases t <;>
    simp

def binaryGate (a : Fin 2) : Circuit.SUM (ZMod 2) 3 (Fin 6 × Fin 2) where
  control := (⟨a.val + 1, by omega⟩, 0)
  target := (⟨a.val + 3, by omega⟩, 1)
  displacement := 0
  weight := 1
  distinct := by intro h; have := congrArg (fun x => x.1.val) h; dsimp at this; omega

def binaryWord : List (Circuit.SUM (ZMod 2) 3 (Fin 6 × Fin 2)) :=
  [binaryGate 0, binaryGate 1]

theorem binaryGate_is_CNOT (g : Fin 2) (a b : ZMod 2) :
    (binaryGate g).localAction a b = (a, b + a) := by
  simp [Circuit.SUM.localAction, binaryGate]

private theorem binaryGate_zMatrix (a : Fin 2) :
    (binaryGate a).zMatrix = 1 + Matrix.single
      (⟨a.val + 1, by omega⟩, 0) (⟨a.val + 3, by omega⟩, 1) 1 := by
  rw [Circuit.SUM.zMatrix_formula]
  simp only [binaryGate, neg_zero, sub_eq_add_neg, Matrix.single_neg,
    ← AddMonoidAlgebra.single_neg, show (-1 : ZMod 2) = 1 from by decide]
  rfl

/-- The exact Pauli Z action of the displayed CNOTs is the constructed shear. -/
theorem binaryWord_action : Circuit.zAction binaryWord = quditMatrix 2 := by
  rw [quditMatrix, binary_quditN]
  simp only [binaryWord, Circuit.zAction_cons, Circuit.zAction_nil,
    binaryGate_zMatrix, Matrix.mul_one]
  have h : (Matrix.single (1, 0) (3, 1) 1 :
      Matrix (Fin 6 × Fin 2) (Fin 6 × Fin 2) (Laurent (ZMod 2) 3)) *
        Matrix.single (2, 0) (4, 1) 1 = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _ (by decide) _
  change (1 + Matrix.single (1, 0) (3, 1) 1) *
    (1 + Matrix.single (2, 0) (4, 1) 1) = _
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, h, add_zero]
  abel

/-- All distinct gate instances have disjoint endpoint sets, including
instances from different families in the same cell. This is physical depth one. -/
theorem binary_parallel (a b : Fin 2) (n m : Translation 3) (h : (a, n) ≠ (b, m)) :
    (binaryGate a).source n ≠ (binaryGate b).source m ∧
    (binaryGate a).source n ≠ (binaryGate b).destination m ∧
    (binaryGate a).destination n ≠ (binaryGate b).source m ∧
    (binaryGate a).destination n ≠ (binaryGate b).destination m := by
  have ha := a.isLt
  have hb := b.isLt
  constructor
  · intro he
    have hv := congrArg (fun x => x.1.1.val) he
    have hn := congrArg Prod.snd he
    have hab : a = b := by apply Fin.ext; dsimp [Circuit.SUM.source, binaryGate] at hv; omega
    exact h (Prod.ext hab hn)
  constructor
  · intro he
    have hv := congrArg (fun x => x.1.1.val) he
    dsimp [Circuit.SUM.source, Circuit.SUM.destination, binaryGate] at hv
    omega
  constructor
  · intro he
    have hv := congrArg (fun x => x.1.1.val) he
    dsimp [Circuit.SUM.source, Circuit.SUM.destination, binaryGate] at hv
    omega
  · intro he
    have hv := congrArg (fun x => x.1.1.val) he
    have hn := congrArg Prod.snd he
    have hab : a = b := by apply Fin.ext; dsimp [Circuit.SUM.destination, binaryGate] at hv; omega
    have hnm : n = m := by simpa [Circuit.SUM.destination, binaryGate] using hn
    exact h (Prod.ext hab hnm)

/-- The one parallel CNOT layer transforms both actual stabilizer images,
with no added qubit species. -/
theorem binary_noAncilla_transport :
    PhysicalIsomorphism.Transports (binaryWord.map Circuit.Layer.sum) (Equiv.refl _)
      (expandMatrix 2 (Glued.xChecks (ZMod 2)))
      (expandMatrix 2 (Glued.splitX (ZMod 2)))
      (expandMatrix 2 (Glued.zGenerators (ZMod 2)))
      (expandMatrix 2 (Glued.splitZ (ZMod 2))) := by
  have hz : Circuit.wordZ (binaryWord.map Circuit.Layer.sum) = quditMatrix 2 := by
    rw [Circuit.wordZ_sum, binaryWord_action]
  have hx := Circuit.wordX_eq_dagger_inverse (binaryWord.map Circuit.Layer.sum)
    (quditMatrix 2) (quditInverse 2) hz (qudit_inverse 2)
  apply PhysicalIsomorphism.transports_of_actions _ (Equiv.refl _)
    _ _ _ _ (quditMatrix 2) (quditInverse 2) (syndromeMatrix 2) (syndromeInverse 2)
    (qudit_inverse 2) (syndrome_inverse 2) (matrix_square 2)
  · intro v
    exact expandMatrix_exact 2 _ _ (Glued.exact_X (ZMod 2)) v
  · intro v
    exact expandMatrix_exact 2 _ _ (Glued.split_exact (ZMod 2)) v
  · simpa using hz
  · simpa using hx

end
end Decoupling.HighDim.GluedDirectional
