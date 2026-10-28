import Decoupling.Circuit

/-!
# Finite CNOT compilation of Laurent shears

There is no bound on polynomial degree in the input, but each input coefficient
has finite support. The lists constructed here are consequently finite, and
the CNOT-family semantics and inverse-dagger conventions come from `Circuit`.
-/

namespace Decoupling.Circuit

open Matrix

noncomputable section

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

def upper (g : Matrix U V R) : Matrix (U ⊕ V) (U ⊕ V) R := fromBlocks 1 g 0 1

omit [Fintype U] [Fintype V] in
@[simp] theorem upper_zero : upper (0 : Matrix U V R) = 1 := by
  simp [upper, Matrix.fromBlocks_one]

theorem upper_add (g h : Matrix U V R) : upper (g + h) = upper g * upper h := by
  simp [upper, Matrix.fromBlocks_multiply, add_comm]

def upperGate (i : U) (j : V) (a : Translation) : CNOT (U ⊕ V) where
  control := Sum.inr j
  target := Sum.inl i
  displacement := a
  distinct := Sum.inr_ne_inl

omit [Fintype U] [Fintype V] in
theorem upperGate_xMatrix (i : U) (j : V) (a : Translation) :
    (upperGate i j a).xMatrix = upper (Matrix.single i j (monomial a)) := by
  funext k l
  cases k <;> cases l <;>
    simp [CNOT.xMatrix, upperGate, upper, Matrix.single_apply, Matrix.one_apply]

def UpperCompilable (g : Matrix U V R) : Prop :=
  ∃ c : List (CNOT (U ⊕ V)), xAction c = upper g

theorem upperCompilable_zero : UpperCompilable (0 : Matrix U V R) :=
  ⟨[], by simp⟩

theorem UpperCompilable.add {g h : Matrix U V R}
    (hg : UpperCompilable g) (hh : UpperCompilable h) : UpperCompilable (g + h) := by
  obtain ⟨c, hc⟩ := hg
  obtain ⟨d, hd⟩ := hh
  exact ⟨c ++ d, by rw [xAction_append, hc, hd, upper_add]⟩

theorem upperCompilable_monomial (i : U) (j : V) (a : Translation) :
    UpperCompilable (Matrix.single i j (monomial a)) :=
  ⟨[upperGate i j a], by simpa using upperGate_xMatrix i j a⟩

theorem upperCompilable_single (i : U) (j : V) (f : R) :
    UpperCompilable (Matrix.single i j f) := by
  rw [← sum_monomials f]
  generalize f.coeff.support.toList = l
  induction l with
  | nil => simpa using (upperCompilable_zero (U := U) (V := V))
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, Matrix.single_add]
    exact (upperCompilable_monomial i j a).add ih

theorem upperCompilable_sum {α : Type*} (s : Finset α) (f : α → Matrix U V R)
    (h : ∀ a ∈ s, UpperCompilable (f a)) : UpperCompilable (∑ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (upperCompilable_zero (U := U) (V := V))
  | @insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self _ _)).add
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

/-- Every finite rectangular Laurent shear is implemented by finitely many
depth-one CNOT families, with no nonempty-rank hypothesis. -/
theorem upper_compilation (g : Matrix U V R) :
    ∃ c : List (CNOT (U ⊕ V)), xAction c = upper g := by
  change UpperCompilable g
  rw [Matrix.matrix_eq_sum_single g]
  apply upperCompilable_sum
  intro i _
  apply upperCompilable_sum
  intro j _
  exact upperCompilable_single i j (g i j)

def lower (f : Matrix V U R) : Matrix (U ⊕ V) (U ⊕ V) R := fromBlocks 1 0 f 1

/-- The opposite shear is compiled by interchanging the two species blocks. -/
theorem lower_compilation (f : Matrix V U R) :
    ∃ c : List (CNOT (U ⊕ V)), xAction c = lower f := by
  obtain ⟨c, hc⟩ := upper_compilation f
  refine ⟨c.map (fun g => g.relabel (Equiv.sumComm V U)), ?_⟩
  rw [xAction_relabel, hc]
  funext i j
  cases i <;> cases j <;> rfl

/-- Both shears in (67), omitting only the separately specified onsite
species permutation, have an actual finite CNOT-family realization. -/
theorem two_shear_compilation (f : Matrix V U R) (g : Matrix U V R) :
    ∃ c : List (CNOT (U ⊕ V)), xAction c = upper g * lower f := by
  obtain ⟨c, hc⟩ := upper_compilation g
  obtain ⟨d, hd⟩ := lower_compilation f
  exact ⟨c ++ d, by rw [xAction_append, hc, hd]⟩

/-- Reverse each CNOT's direction and displacement to realize the shears
in the manuscript's Z-action convention. -/
theorem two_shear_z_compilation (f : Matrix V U R) (g : Matrix U V R) :
    ∃ c : List (CNOT (U ⊕ V)), zAction c = upper g * lower f := by
  obtain ⟨c, hc⟩ := two_shear_compilation f g
  exact ⟨c.map CNOT.dual, by rw [zAction_dual, hc]⟩

end
end Decoupling.Circuit
