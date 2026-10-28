import Decoupling.HighDim.DenseCircuitProgram
import Decoupling.HighDim.CircuitPermutationSize

/-!
# Executable onsite SWAP compilation

Unlike extracting witnesses from IsSwap, this recursion retains the
actual pair (a, sigma a) when it performs the elimination step. It
uses only species-index operations and emits at most one SWAP per
listed species. No field operations or classical choice are executed.
-/
namespace Decoupling.HighDim.DenseCircuitPermutation
open Circuit ArithmeticCost Matrix
variable {ι : Type*} [DecidableEq ι]

def swapList : List ι → Equiv.Perm ι → List (Circuit.SWAP ι)
  | [], _ => []
  | a::l, σ => if ha : a=σ a then swapList l σ else
      ⟨a,σ a,ha⟩ :: swapList l (Equiv.swap a (σ a) * σ)

theorem swapList_length (l : List ι) (σ : Equiv.Perm ι) : (swapList l σ).length ≤ l.length := by
  induction l generalizing σ with
  | nil => simp [swapList]
  | cons a l ih =>
    simp only [swapList]
    split_ifs
    · exact (ih σ).trans (Nat.le_succ _)
    · simpa only [List.length_cons] using Nat.succ_le_succ (ih (Equiv.swap a (σ a)*σ))

variable {K : Type*} [CommRing K] {D : ℕ} [Fintype ι]

theorem swapList_action (l : List ι) (σ : Equiv.Perm ι)
    (hsupport : ∀ x, σ x ≠ x → x ∈ l) :
    Circuit.swapAction (K := K) (D := D) (swapList l σ) = Circuit.permMatrix σ := by
  induction l generalizing σ with
  | nil =>
    have he : σ = 1 := by
      apply Equiv.ext
      intro x
      by_contra hx
      exact List.not_mem_nil (hsupport x hx)
    simp [swapList, he]
  | cons a l ih =>
    unfold swapList
    split_ifs with ha
    · apply ih
      intro x hx
      exact List.mem_of_ne_of_mem (fun hxa => by subst x; exact hx ha.symm) (hsupport x hx)
    · rw [Circuit.swapAction_cons]
      have htail : ∀ x, (Equiv.swap a (σ a)*σ) x ≠ x → x ∈ l := by
        intro x hx
        have hh := Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self hx
        exact List.mem_of_ne_of_mem hh.2 (hsupport x hh.1)
      rw [ih _ htail]
      change Circuit.permMatrix (Equiv.swap a (σ a)) * Circuit.permMatrix (Equiv.swap a (σ a)*σ) = _
      rw [← Circuit.permMatrix_mul, Equiv.swap_mul_self_mul]

/-- Explicit ordered Fin enumeration; even the empty species case is executable. -/
def compileFin (n : ℕ) (σ : Equiv.Perm (Fin n)) : List (Circuit.SWAP (Fin n)) :=
  swapList (List.finRange n) σ

theorem compileFin_length (n : ℕ) (σ : Equiv.Perm (Fin n)) : (compileFin n σ).length ≤ n := by
  simpa only [compileFin, List.length_finRange] using swapList_length (List.finRange n) σ

theorem compileFin_action (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Circuit.swapAction (K := K) (D := D) (compileFin n σ) = Circuit.permMatrix σ :=
  swapList_action _ _ (by intro x _; simp)

/-- The block species enumeration is likewise explicit integer data. -/
def sumEnumeration (m n : ℕ) : List (Fin m ⊕ Fin n) :=
  (List.finRange m).map Sum.inl ++ (List.finRange n).map Sum.inr

def compileSum (m n : ℕ) (σ : Equiv.Perm (Fin m ⊕ Fin n)) : List (Circuit.SWAP (Fin m ⊕ Fin n)) :=
  swapList (sumEnumeration m n) σ

theorem compileSum_length (m n : ℕ) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    (compileSum m n σ).length ≤ m+n := by
  simpa [compileSum, sumEnumeration] using swapList_length (sumEnumeration m n) σ

theorem compileSum_action (m n : ℕ) (σ : Equiv.Perm (Fin m ⊕ Fin n)) :
    Circuit.swapAction (K := K) (D := D) (compileSum m n σ) = Circuit.permMatrix σ := by
  apply swapList_action
  intro x _
  cases x <;> simp [sumEnumeration]

/-- SWAP compilation executes no field operation; its physical length is
counted separately above and is not discarded from circuit depth. -/
def program (n : ℕ) (σ : Equiv.Perm (Fin n)) : Work K (List (Circuit.Layer K D (Fin n))) :=
  Work.pure ((compileFin n σ).map Circuit.Layer.swap)

omit [CommRing K] in
@[simp] theorem program_cost (n : ℕ) (σ : Equiv.Perm (Fin n)) : (program (K := K) (D := D) n σ).cost = 0 := rfl

omit [CommRing K] in
theorem program_length (n : ℕ) (σ : Equiv.Perm (Fin n)) : (program (K := K) (D := D) n σ).value.length ≤ n := by
  simpa [program] using compileFin_length n σ

theorem program_z (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    Circuit.wordZ (program (K := K) (D := D) n σ).value = Circuit.permMatrix σ := by
  rw [program, Work.pure_value, Circuit.wordZ_swap, compileFin_action]

end Decoupling.HighDim.DenseCircuitPermutation
