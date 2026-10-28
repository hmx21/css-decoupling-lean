import Decoupling.HighDim.CircuitPermutationSize
import Mathlib.Data.Int.Interval

/-! # HD012 dense coefficient boxes and their actual circuit-size bounds -/
namespace Decoupling.HighDim.LaurentBoxes
open Matrix
noncomputable section

def box (D h : ℕ) : Finset (Translation D) :=
  Fintype.piFinset (fun _ : Fin D => Finset.Icc (-(h : ℤ)) (h : ℤ))

@[simp] theorem mem_box {D h : ℕ} (a : Translation D) :
    a ∈ box D h ↔ ∀ i, -(h : ℤ) ≤ a i ∧ a i ≤ (h : ℤ) := by
  simp [box]

theorem card_box (D h : ℕ) : (box D h).card = (2 * h + 1) ^ D := by
  have hc : ((h : ℤ) + 1 + (h : ℤ)).toNat = 2 * h + 1 := by omega
  simp [box, Fintype.card_piFinset, Int.card_Icc, hc]

variable {K : Type*} [CommRing K] {D : ℕ}

def Supported (f : Laurent K D) (h : ℕ) : Prop := f.coeff.support ⊆ box D h

theorem support_card_le (f : Laurent K D) (h : ℕ) (hf : Supported f h) :
    f.coeff.support.card ≤ (2 * h + 1) ^ D :=
  (Finset.card_le_card hf).trans_eq (card_box D h)

variable {U V : Type*} [Fintype U] [Fintype V]

def MatrixSupported (A : Matrix U V (Laurent K D)) (h : ℕ) : Prop := ∀ i j, Supported (A i j) h

theorem matrix_supportSize_le (A : Matrix U V (Laurent K D)) (h : ℕ) (hA : MatrixSupported A h) :
    Circuit.supportSize A ≤ Fintype.card U * Fintype.card V * (2 * h + 1) ^ D := by
  calc
    _ ≤ ∑ _i : U, ∑ _j : V, (2 * h + 1) ^ D := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact support_card_le _ h (hA i j)
    _ = _ := by simp [mul_assoc]

variable [DecidableEq U] [DecidableEq V]

/-- Dense box counts bound the length of an actual verified Θ circuit.
The onsite permutation overhead is explicitly retained. -/
theorem theta_circuit_dense_bound (f : Matrix V U (Laurent K D)) (g : Matrix U V (Laurent K D))
    (h : ℕ) (hf : MatrixSupported f h) (hg : MatrixSupported g h)
    (e : (U ⊕ V) ≃ (V ⊕ U)) :
    ∃ c : List (Circuit.Layer K D (V ⊕ U)),
      Circuit.wordZ c = (Stabilization.theta f g).submatrix id e.symm ∧
      Circuit.wordX c = dagger ((Stabilization.theta g f).submatrix e.symm id) ∧
      c.length ≤ 2 * (Fintype.card U * Fintype.card V * (2 * h + 1) ^ D) +
        Fintype.card U + Fintype.card V := by
  obtain ⟨c, hz, hx, hl⟩ := Circuit.theta_circuit_size f g e
  refine ⟨c, hz, hx, ?_⟩
  have hf' := matrix_supportSize_le f h hf
  have hg' := matrix_supportSize_le g h hg
  rw [Nat.mul_comm (Fintype.card V) (Fintype.card U)] at hf'
  omega

end
end Decoupling.HighDim.LaurentBoxes
