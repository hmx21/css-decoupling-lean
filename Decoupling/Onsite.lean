import Decoupling.ShearCompile
import Mathlib.GroupTheory.Perm.Sign

/-! Finite onsite species permutations, realized by SWAPs (three onsite CNOTs each). -/

namespace Decoupling.Circuit

open Matrix

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A permutation matrix sends source species j to target species σ(j). -/
def permMatrix (σ : Equiv.Perm ι) : Matrix ι ι R := (1 : Matrix ι ι R).submatrix σ.symm id

omit [Fintype ι] in
theorem permMatrix_apply (σ : Equiv.Perm ι) (i j : ι) :
    permMatrix σ i j = if i = σ j then 1 else 0 := by
  simp [permMatrix, Matrix.one_apply, Equiv.symm_apply_eq]

@[simp] theorem permMatrix_mulVec (σ : Equiv.Perm ι) (p : ι → R) :
    permMatrix σ *ᵥ p = p ∘ σ.symm := by
  simpa [permMatrix] using
    (Matrix.submatrix_mulVec_equiv (1 : Matrix ι ι R) p σ.symm (Equiv.refl ι))

omit [Fintype ι] in
@[simp] theorem permMatrix_one : permMatrix (1 : Equiv.Perm ι) = 1 := rfl

theorem permMatrix_mul (σ τ : Equiv.Perm ι) :
    permMatrix (σ * τ) = permMatrix σ * permMatrix τ := by
  apply Matrix.ext_iff_mulVec.mpr
  intro p
  simp only [← Matrix.mulVec_mulVec, permMatrix_mulVec]
  rfl

def onsiteCNOT (i j : ι) (h : i ≠ j) : CNOT ι where
  control := j
  target := i
  displacement := 0
  distinct := Ne.symm h

def swapWord (i j : ι) (h : i ≠ j) : List (CNOT ι) :=
  [onsiteCNOT i j h, onsiteCNOT j i (Ne.symm h), onsiteCNOT i j h]

/-- The standard three-CNOT implementation of an onsite SWAP. -/
theorem swapWord_action (i j : ι) (h : i ≠ j) :
    xAction (swapWord i j h) = permMatrix (Equiv.swap i j) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro p
  simp only [swapWord, xAction_cons, xAction_nil, Matrix.mul_one,
    ← Matrix.mulVec_mulVec, permMatrix_mulVec]
  funext k
  by_cases hi : k = i
  · subst k
    simp [-Matrix.mulVec_mulVec, CNOT.x_mulVec, onsiteCNOT, h, Ne.symm h,
      ← add_assoc, CharTwo.add_cancel_right]
  · by_cases hj : k = j
    · subst k
      simp [-Matrix.mulVec_mulVec, CNOT.x_mulVec, onsiteCNOT, Ne.symm h, add_left_comm]
    · simp [-Matrix.mulVec_mulVec, CNOT.x_mulVec, onsiteCNOT, hi, hj,
        Equiv.swap_apply_of_ne_of_ne]

/-- Any finite species permutation is a finite circuit of onsite gates.
The matrix convention includes the direction of the permutation explicitly. -/
theorem permutation_compilation (σ : Equiv.Perm ι) :
    ∃ c : List (CNOT ι), xAction c = permMatrix σ ∧
      ∀ g ∈ c, g.displacement = 0 := by
  induction σ using Equiv.Perm.swap_induction_on with
  | one => exact ⟨[], by simp, by simp⟩
  | swap_mul σ i j hij ih =>
    obtain ⟨c, hc, hz⟩ := ih
    refine ⟨swapWord i j hij ++ c, ?_, ?_⟩
    · rw [xAction_append, swapWord_action, hc, permMatrix_mul]
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · simp only [swapWord, List.mem_cons, List.not_mem_nil, or_false] at hg
        rcases hg with rfl | rfl | rfl <;> rfl
      · exact hz g hg

end
end Decoupling.Circuit
