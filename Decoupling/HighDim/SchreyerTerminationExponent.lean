import Decoupling.HighDim.SchreyerModule
import Mathlib.Tactic

/-!
# Exponent arithmetic in Schreyer's finite-length argument

Only leading exponents are constrained: polynomial vectors and their
lower terms may be inhomogeneous. A lexicographically earlier leading
monomial contributes the lcm quotient on the earlier source position.
That quotient omits one more variable. With one variable remaining,
minimal same-position leading terms are comparable, hence unique.
These are arithmetic lemmas; they do not assume or assert that an arbitrary
kernel-generator algorithm produces a Schreyer resolution.
-/
namespace Decoupling.HighDim.SchreyerTermination
open SchreyerModule
variable {D : ℕ}

/-- Vanishing on the first k variables, with the natural coordinate order. -/
def MissingPrefix (k : ℕ) (a : Exponent D) : Prop :=
  ∀ i : Fin D, i.val < k → a i = 0

/-- The usual descending lexicographic comparison, expressed by its first
strictly different coordinate. It is independent of the module term order. -/
def LexGE (a b : Exponent D) : Prop :=
  a=b ∨ ∃ i : Fin D, (∀ j : Fin D, j < i → a j=b j) ∧ b i<a i

@[simp] theorem missingPrefix_zero (a : Exponent D) : MissingPrefix 0 a := by
  intro i hi
  omega

theorem missingPrefix_mono {k l : ℕ} {a : Exponent D}
    (ha : MissingPrefix l a) (hkl : k ≤ l) : MissingPrefix k a :=
  fun i hi => ha i (lt_of_lt_of_le hi hkl)

theorem missingPrefix_sup {k : ℕ} {a b : Exponent D}
    (ha : MissingPrefix k a) (hb : MissingPrefix k b) : MissingPrefix k (a ⊔ b) := by
  intro i hi
  simp only [Finsupp.sup_apply,ha i hi,hb i hi,sup_idem]

theorem missingPrefix_tsub {k : ℕ} {a b : Exponent D}
    (ha : MissingPrefix k a) : MissingPrefix k (a-b) := by
  intro i hi
  rw [Finsupp.tsub_apply,ha i hi,Nat.zero_sub]

/-- After an equal initial prefix, descending lexicographic order forces
weak descent at the next coordinate. -/
theorem lexGE_next_le {k : ℕ} {a b : Exponent D}
    (ha : MissingPrefix k a) (hb : MissingPrefix k b) (hab : LexGE a b)
    (i : Fin D) (hi : i.val=k) : b i ≤ a i := by
  rcases hab with rfl | ⟨j,hprefix,hstrict⟩
  · exact le_rfl
  · by_cases hj : j.val < k
    · rw [ha j hj,hb j hj] at hstrict
      omega
    · by_cases hji : j=i
      · subst j
        exact Nat.le_of_lt hstrict
      · have hij : i < j := by
          have hne : j.val ≠ i.val := fun h => hji (Fin.ext h)
          change i.val < j.val
          omega
        exact (hprefix i hij).symm.le

/-- The actual lcm quotient on the earlier generator omits the next
variable. No condition on lower polynomial terms is present. -/
theorem lcmQuotient_missing_succ {k : ℕ} {a b : Exponent D}
    (ha : MissingPrefix k a) (hb : MissingPrefix k b) (hab : LexGE a b) :
    MissingPrefix (k+1) ((a ⊔ b)-a) := by
  intro i hi
  by_cases hik : i.val < k
  · have h := missingPrefix_tsub (b := a) (missingPrefix_sup ha hb)
    exact h i hik
  · have he : i.val=k := by omega
    have hba := lexGE_next_le ha hb hab i he
    rw [Finsupp.tsub_apply,Finsupp.sup_apply,sup_eq_left.mpr hba,Nat.sub_self]

/-- With at most one variable left, monomial divisibility is total. -/
theorem terminal_exponents_comparable {a b : Exponent D}
    (ha : MissingPrefix (D-1) a) (hb : MissingPrefix (D-1) b) : a ≤ b ∨ b ≤ a := by
  by_cases hD : D=0
  · subst D
    left
    intro i
    exact Fin.elim0 i
  · let last : Fin D := ⟨D-1,by omega⟩
    have hat (i : Fin D) (hi : ¬i.val<D-1) : i=last := by
      apply Fin.ext
      have := i.isLt
      dsimp [last]
      omega
    rcases le_total (a last) (b last) with hab | hba
    · left
      intro i
      by_cases hi : i.val<D-1
      · rw [ha i hi,hb i hi]
      · rw [hat i hi]
        exact hab
    · right
      intro i
      by_cases hi : i.val<D-1
      · rw [ha i hi,hb i hi]
      · rw [hat i hi]
        exact hba

/-- Minimal leading monomials with one variable remaining have distinct
module positions. The antichain premise will be established by actual
Gröbner-basis minimization, not assumed of the input module. -/
theorem terminal_positions_injective {r m : ℕ} (t : Fin m → Term D r)
    (hmissing : ∀ i, MissingPrefix (D-1) (t i).1)
    (hminimal : ∀ i j, i≠j → (t i).2=(t j).2 → ¬(t i).1≤(t j).1) :
    Function.Injective (fun i => (t i).2) := by
  intro i j hij
  by_contra hne
  rcases terminal_exponents_comparable (hmissing i) (hmissing j) with h | h
  · exact hminimal i j hne hij h
  · exact hminimal j i (Ne.symm hne) hij.symm h

end Decoupling.HighDim.SchreyerTermination
