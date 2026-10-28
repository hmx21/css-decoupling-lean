import Decoupling.HighDim.BlockCircuit
import Mathlib.Data.Fintype.BigOperators

/-!
# HD012 actual gate-word bounds from Laurent matrix supports

The length bound is attached to the very word whose matrix action is
proved. It does not infer a circuit bound just from matrix dimensions.
The separate Algorithm 2 complexity proof must still bound the input
shear supports; no such bound is assumed as an original-code hypothesis.
-/
namespace Decoupling.HighDim.Circuit
open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [CommRing K] {D : ℕ}
  {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

def supportSize (g : Matrix U V (Laurent K D)) : ℕ :=
  ∑ i, ∑ j, (g i j).coeff.support.card

def UpperBudget (g : Matrix U V (Laurent K D)) (n : ℕ) : Prop :=
  ∃ c : List (SUM K D (U ⊕ V)), xAction c = upper g ∧ c.length ≤ n

theorem upperBudget_zero : UpperBudget (0 : Matrix U V (Laurent K D)) 0 := by
  exact ⟨[], by simp, by simp⟩

theorem UpperBudget.add {g h : Matrix U V (Laurent K D)} {n m : ℕ}
    (hg : UpperBudget g n) (hh : UpperBudget h m) : UpperBudget (g + h) (n + m) := by
  obtain ⟨c, hc, hn⟩ := hg
  obtain ⟨d, hd, hm⟩ := hh
  exact ⟨c ++ d, by rw [xAction_append, hc, hd, upper_add], by simpa using Nat.add_le_add hn hm⟩

theorem upperBudget_monomial (i : U) (j : V) (a : Translation D) (v : K) :
    UpperBudget (Matrix.single i j (AddMonoidAlgebra.single a v)) 1 :=
  ⟨[upperGate i j a v], by simpa using upperGate_xMatrix i j a v, le_rfl⟩

theorem upperBudget_single (i : U) (j : V) (f : Laurent K D) :
    UpperBudget (Matrix.single i j f) f.coeff.support.card := by
  have h : ∀ l : List (Translation D),
      UpperBudget (Matrix.single i j ((l.map fun a => AddMonoidAlgebra.single a (f.coeff a)).sum)) l.length := by
    intro l
    induction l with
    | nil => simpa using (upperBudget_zero (K := K) (D := D) (U := U) (V := V))
    | cons a l ih =>
      simpa [Nat.add_comm, Matrix.single_add] using
        (upperBudget_monomial i j a (f.coeff a)).add ih
  have hl := h f.coeff.support.toList
  rw [sum_weighted_monomials f, Finset.length_toList] at hl
  exact hl

theorem upperBudget_sum {α : Type*} (s : Finset α) (g : α → Matrix U V (Laurent K D))
    (n : α → ℕ) (h : ∀ a ∈ s, UpperBudget (g a) (n a)) :
    UpperBudget (∑ a ∈ s, g a) (∑ a ∈ s, n a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (upperBudget_zero (K := K) (D := D) (U := U) (V := V))
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

/-- Every actual shear has a word with at most one SUM layer per stored
nonzero Laurent monomial, including empty rectangular matrices. -/
theorem upper_compilation_size (g : Matrix U V (Laurent K D)) :
    UpperBudget g (supportSize g) := by
  conv_lhs => rw [Matrix.matrix_eq_sum_single g]
  apply upperBudget_sum
  intro i _
  apply upperBudget_sum
  intro j _
  exact upperBudget_single i j (g i j)

theorem lower_compilation_size (f : Matrix V U (Laurent K D)) :
    ∃ c : List (SUM K D (U ⊕ V)), xAction c = lower f ∧ c.length ≤ supportSize f := by
  obtain ⟨c, hc, hn⟩ := upper_compilation_size f
  refine ⟨c.map (fun g => g.relabel (Equiv.sumComm V U)), ?_, by simpa using hn⟩
  rw [xAction_relabel, hc]
  funext i j
  cases i <;> cases j <;> rfl

theorem two_shear_z_compilation_size
    (f : Matrix V U (Laurent K D)) (g : Matrix U V (Laurent K D)) :
    ∃ c : List (SUM K D (U ⊕ V)), zAction c = upper g * lower f ∧
      c.length ≤ supportSize g + supportSize f := by
  obtain ⟨a, ha, hna⟩ := upper_compilation_size g
  obtain ⟨b, hb, hnb⟩ := lower_compilation_size f
  refine ⟨(a ++ b).map SUM.dual, ?_, ?_⟩
  · rw [zAction_dual, xAction_append, ha, hb]
  · simpa only [List.length_map, List.length_append] using Nat.add_le_add hna hnb

end
end Decoupling.HighDim.Circuit
