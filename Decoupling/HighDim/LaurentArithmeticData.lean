import Decoupling.HighDim.LaurentBoxesOperations
import Decoupling.HighDim.ArithmeticCost
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# HD012 dense Laurent coefficients with explicit integer-box indexing

The executable representation is a finite coefficient array. Indexing and
out-of-box lookups use only integer arithmetic. The Laurent-polynomial
denotation is a semantic interface, not an uncounted arithmetic program.
-/
namespace Decoupling.HighDim.LaurentArithmetic
set_option backward.isDefEq.respectTransparency false
def boxSize (D h : ℕ) : ℕ := (2 * h + 1) ^ D

def exponentAt (D h : ℕ) (k : Fin (boxSize D h)) : Translation D :=
  fun i => (((finFunctionFinEquiv (m := 2 * h + 1) (n := D)).symm k i).val : ℤ) - h

theorem exponentAt_mem (D h : ℕ) (k : Fin (boxSize D h)) :
    exponentAt D h k ∈ LaurentBoxes.box D h := by
  rw [LaurentBoxes.mem_box]
  intro i
  have hi := ((finFunctionFinEquiv (m := 2 * h + 1) (n := D)).symm k i).isLt
  dsimp [exponentAt]
  constructor <;> omega

def exponentIndex {D h : ℕ} (a : Translation D)
    (ha : a ∈ LaurentBoxes.box D h) : Fin (boxSize D h) :=
  finFunctionFinEquiv (fun i => (⟨(a i + h).toNat, by
    have hi := (LaurentBoxes.mem_box a).mp ha i
    omega⟩ : Fin (2 * h + 1)))

@[simp] theorem exponentAt_index {D h : ℕ} (a : Translation D)
    (ha : a ∈ LaurentBoxes.box D h) :
    exponentAt D h (exponentIndex a ha) = a := by
  funext i
  have hi := (LaurentBoxes.mem_box a).mp ha i
  simp only [exponentAt, exponentIndex, Equiv.symm_apply_apply]
  omega

@[simp] theorem exponentIndex_at {D h : ℕ} (k : Fin (boxSize D h)) :
    exponentIndex (exponentAt D h k) (exponentAt_mem D h k) = k := by
  apply (finFunctionFinEquiv (m := 2 * h + 1) (n := D)).symm.injective
  funext i
  apply Fin.ext
  simp only [exponentIndex, Equiv.symm_apply_apply, exponentAt]
  omega

theorem exponentAt_injective (D h : ℕ) : Function.Injective (exponentAt D h) := by
  intro i j he
  have hh := congrArg (fun a : {a // a ∈ LaurentBoxes.box D h} =>
    exponentIndex a.val a.property) (show
      (⟨exponentAt D h i, exponentAt_mem D h i⟩ : {a // a ∈ LaurentBoxes.box D h}) =
        ⟨exponentAt D h j, exponentAt_mem D h j⟩ from Subtype.ext he)
  simpa using hh

variable {K : Type*} [CommRing K] {D h : ℕ}

abbrev Dense (K : Type*) (D h : ℕ) := Vector K (boxSize D h)

def lookup (v : Dense K D h) (a : Translation D) : K :=
  if ha : a ∈ LaurentBoxes.box D h then v[exponentIndex a ha] else 0

@[simp] theorem lookup_at (v : Dense K D h) (k : Fin (boxSize D h)) :
    lookup v (exponentAt D h k) = v[k] := by
  rw [lookup, dite_eq_left (exponentAt_mem D h k)]
  simp

/-- Genuine Laurent polynomial represented by the dense coefficient array. -/
noncomputable def denote (v : Dense K D h) : Laurent K D :=
  ∑ k, AddMonoidAlgebra.single (exponentAt D h k) v[k]

theorem denote_coeff (v : Dense K D h) (a : Translation D) :
    (denote v).coeff a = lookup v a := by
  classical
  simp only [denote, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply,
    AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases ha : a ∈ LaurentBoxes.box D h
  · rw [lookup, dite_eq_left ha, Finset.sum_eq_single (exponentIndex a ha)]
    · simp
    · intro k _ hk
      have he : exponentAt D h k ≠ a := by
        intro he
        apply hk
        apply exponentAt_injective D h
        rw [he, exponentAt_index]
      simp [he]
    · simp
  · rw [lookup, dite_eq_right ha]
    apply Finset.sum_eq_zero
    intro k _
    have he : exponentAt D h k ≠ a := by
      intro he
      exact ha (he ▸ exponentAt_mem D h k)
    simp [he]

theorem denote_supported (v : Dense K D h) : LaurentBoxes.Supported (denote v) h := by
  intro a ha
  by_contra hn
  have hz : (denote v).coeff a = 0 := by rw [denote_coeff]; simp [lookup, hn]
  exact Finsupp.mem_support_iff.mp ha hz

theorem denote_eq_of_coeff (v : Dense K D h) (f : Laurent K D)
    (hf : LaurentBoxes.Supported f h)
    (he : ∀ k, f.coeff (exponentAt D h k) = v[k]) : denote v = f := by
  ext a
  rw [denote_coeff]
  by_cases ha : a ∈ LaurentBoxes.box D h
  · rw [lookup, dite_eq_left ha, ← he (exponentIndex a ha), exponentAt_index]
  · rw [lookup, dite_eq_right ha]
    apply Eq.symm
    apply Finsupp.notMem_support_iff.mp
    exact fun hmem => ha (hf hmem)

end Decoupling.HighDim.LaurentArithmetic
