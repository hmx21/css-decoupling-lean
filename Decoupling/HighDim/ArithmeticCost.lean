import Mathlib.Data.Matrix.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Executable field operations with their actual trace

HD012, polynomial-cost proposition. Every field operation and zero test
is recorded with its actual operands. `Work.bind` concatenates the traces
of the computations actually executed. Cost is trace length, not a
separately assigned estimate. Dense collection materializes its values.
-/

namespace Decoupling.HighDim.ArithmeticCost

universe u v w

inductive Operation (K : Type u) where
  | add (x y : K)
  | sub (x y : K)
  | mul (x y : K)
  | div (x y : K)
  | neg (x : K)
  | testZero (x : K)
  deriving Repr

structure Work (K : Type u) (α : Type v) where
  value : α
  trace : List (Operation K)

namespace Work
variable {K : Type u} {α : Type v} {β : Type w}

def pure (x : α) : Work K α := ⟨x, []⟩

def bind (x : Work K α) (f : α → Work K β) : Work K β :=
  let y := f x.value
  ⟨y.value, x.trace ++ y.trace⟩

instance : Monad (Work K) where
  pure := pure
  bind := bind

def cost (x : Work K α) : ℕ := x.trace.length

@[simp] theorem pure_value (x : α) : (pure (K := K) x).value = x := rfl
@[simp] theorem pure_cost (x : α) : (pure (K := K) x).cost = 0 := rfl
@[simp] theorem bind_value (x : Work K α) (f : α → Work K β) :
    (bind x f).value = (f x.value).value := rfl
@[simp] theorem bind_cost (x : Work K α) (f : α → Work K β) :
    (bind x f).cost = x.cost + (f x.value).cost := List.length_append

end Work

variable {K : Type u} [Field K] [DecidableEq K]

def add (x y : K) : Work K K := ⟨x + y, [.add x y]⟩
def sub (x y : K) : Work K K := ⟨x - y, [.sub x y]⟩
def mul (x y : K) : Work K K := ⟨x * y, [.mul x y]⟩
def div (x y : K) : Work K K := ⟨x / y, [.div x y]⟩
def neg (x : K) : Work K K := ⟨-x, [.neg x]⟩
def testZero (x : K) : Work K Bool := ⟨decide (x = 0), [.testZero x]⟩


omit [DecidableEq K] in
@[simp] theorem add_value (x y : K) : (add x y).value = x + y := rfl
omit [DecidableEq K] in
@[simp] theorem sub_value (x y : K) : (sub x y).value = x - y := rfl
omit [DecidableEq K] in
@[simp] theorem mul_value (x y : K) : (mul x y).value = x * y := rfl
omit [DecidableEq K] in
@[simp] theorem div_value (x y : K) : (div x y).value = x / y := rfl
omit [DecidableEq K] in
@[simp] theorem neg_value (x : K) : (neg x).value = -x := rfl
@[simp] theorem testZero_value (x : K) : (testZero x).value = decide (x = 0) := rfl
omit [DecidableEq K] in
@[simp] theorem add_cost (x y : K) : (add x y).cost = 1 := rfl
omit [DecidableEq K] in
@[simp] theorem sub_cost (x y : K) : (sub x y).cost = 1 := rfl
omit [DecidableEq K] in
@[simp] theorem mul_cost (x y : K) : (mul x y).cost = 1 := rfl
omit [DecidableEq K] in
@[simp] theorem div_cost (x y : K) : (div x y).cost = 1 := rfl
omit [DecidableEq K] in
@[simp] theorem neg_cost (x : K) : (neg x).cost = 1 := rfl
@[simp] theorem testZero_cost (x : K) : (testZero x).cost = 1 := rfl

def prepend {α : Type v} {n : ℕ} (x : α) (v : Vector α n) : Vector α (n + 1) :=
  Vector.ofFn (Fin.cases x (fun i => v[i]))

@[simp] theorem prepend_zero {α : Type v} {n : ℕ} (x : α) (v : Vector α n) :
    (prepend x v)[0] = x := by simp [prepend]

@[simp] theorem prepend_succ {α : Type v} {n : ℕ} (x : α) (v : Vector α n) (i : Fin n) :
    (prepend x v)[i.succ] = v[i] := by simp [prepend]

/-- Execute each supplied computation once and retain the dense values. -/
def collect {α : Type v} : (n : ℕ) → (Fin n → Work K α) → Work K (Vector α n)
  | 0, _ => Work.pure #v[]
  | n + 1, f => Work.bind (f 0) fun x =>
      Work.bind (collect n (fun i => f i.succ)) fun xs => Work.pure (prepend x xs)

omit [Field K] [DecidableEq K] in
@[simp] theorem collect_value_get {α : Type v} : ∀ (n : ℕ) (f : Fin n → Work K α) (i : Fin n),
    (collect n f).value[i] = (f i).value := by
  intro n
  induction n with
  | zero => intro f i; exact Fin.elim0 i
  | succ n ih =>
    intro f i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [collect]
    · change (prepend (f 0).value (collect n (fun j => f j.succ)).value)[i.succ] = _
      rw [prepend_succ, ih]

omit [Field K] [DecidableEq K] in
@[simp] theorem collect_value_get_nat {α : Type v} (n : ℕ) (f : Fin n → Work K α)
    (i : ℕ) (hi : i < n) : (collect n f).value[i] = (f ⟨i, hi⟩).value :=
  collect_value_get n f ⟨i, hi⟩

omit [Field K] [DecidableEq K] in
@[simp] theorem collect_cost {α : Type v} : ∀ (n : ℕ) (f : Fin n → Work K α),
    (collect n f).cost = ∑ i : Fin n, (f i).cost := by
  intro n
  induction n with
  | zero => intro f; simp [collect]
  | succ n ih => intro f; simp [collect, ih, Fin.sum_univ_succ]

/-- A recursive dot product whose additions and multiplications are
precisely the operations in its returned trace. -/
def dot : (n : ℕ) → (Fin n → K) → (Fin n → K) → Work K K
  | 0, _, _ => Work.pure 0
  | n + 1, v, w => Work.bind (mul (v 0) (w 0)) fun a =>
      Work.bind (dot n (fun i => v i.succ) (fun i => w i.succ)) fun b => add a b

omit [DecidableEq K] in
@[simp] theorem dot_value : ∀ (n : ℕ) (v w : Fin n → K),
    (dot n v w).value = ∑ i, v i * w i := by
  intro n
  induction n with
  | zero => intro v w; simp [dot]
  | succ n ih => intro v w; simp [dot, ih, mul, add, Fin.sum_univ_succ]

omit [DecidableEq K] in
@[simp] theorem dot_cost : ∀ (n : ℕ) (v w : Fin n → K), (dot n v w).cost = 2 * n := by
  intro n
  induction n with
  | zero => intro v w; rfl
  | succ n ih =>
    intro v w
    simp only [dot, Work.bind_cost, mul_cost, add_cost, ih]
    omega

/-- Scan a dense column in its fixed finite order. Zero tests are
counted too, making the arithmetic-operation bound conservative. -/
def firstNonzero : (m : ℕ) → (Fin m → K) → Work K (Option (Fin m))
  | 0, _ => Work.pure none
  | m + 1, v => Work.bind (testZero (v 0)) fun z =>
      if z then Work.bind (firstNonzero m (fun i => v i.succ)) fun r =>
        Work.pure (r.map Fin.succ)
      else Work.pure (some 0)

theorem firstNonzero_cost : ∀ (m : ℕ) (v : Fin m → K), (firstNonzero m v).cost ≤ m := by
  intro m
  induction m with
  | zero => intro v; rfl
  | succ m ih =>
    intro v
    by_cases h : v 0 = 0
    · have hh := ih (fun i => v i.succ)
      simp [firstNonzero, h]
      omega
    · simp [firstNonzero, h]

theorem firstNonzero_none : ∀ (m : ℕ) (v : Fin m → K),
    (firstNonzero m v).value = none ↔ ∀ i, v i = 0 := by
  intro m
  induction m with
  | zero => intro v; simp [firstNonzero]
  | succ m ih =>
    intro v
    by_cases h : v 0 = 0
    · simp only [firstNonzero, Work.bind_value, testZero_value, h, decide_true, ite_true,
        Work.pure_value, Option.map_eq_none_iff, ih]
      exact ⟨fun ht i => Fin.cases h ht i, fun ht i => ht i.succ⟩
    · simp [firstNonzero, h, show ¬ (∀ i, v i = 0) from fun hh => h (hh 0)]

theorem firstNonzero_some : ∀ (m : ℕ) (v : Fin m → K) (r : Fin m),
    (firstNonzero m v).value = some r → v r ≠ 0 := by
  intro m
  induction m with
  | zero => intro v r; exact Fin.elim0 r
  | succ m ih =>
    intro v r hr
    by_cases h : v 0 = 0
    · simp only [firstNonzero, Work.bind_value, testZero_value, h, decide_true, ite_true,
        Work.pure_value, Option.map_eq_some_iff] at hr
      obtain ⟨s, hs, rfl⟩ := hr
      exact ih _ _ hs
    · have hr0 : (0 : Fin (m + 1)) = r := by simpa [firstNonzero, h] using hr
      exact hr0 ▸ h

end Decoupling.HighDim.ArithmeticCost
