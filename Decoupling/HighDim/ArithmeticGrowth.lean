import Decoupling.HighDim.ArithmeticCost
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# HD012 composing proved arithmetic size bounds

These expressions denote ordinary natural-coefficient polynomials.
The execution lemmas concern actual Work.bind traces. They are bookkeeping
helpers: every step bound and the number of steps must still be proved
for the concrete decoupling construction, not assumed in its final theorem.
-/
namespace Decoupling.HighDim.ArithmeticGrowth
open ArithmeticCost

inductive Expression where
  | constant (c : ℕ)
  | input
  | add (p q : Expression)
  | mul (p q : Expression)
  | pow (p : Expression) (n : ℕ)

def Expression.eval : Expression → ℕ → ℕ
  | .constant c, _ => c
  | .input, s => s
  | .add p q, s => p.eval s + q.eval s
  | .mul p q, s => p.eval s * q.eval s
  | .pow p n, s => p.eval s ^ n

noncomputable def Expression.polynomial : Expression → Polynomial ℕ
  | .constant c => Polynomial.C c
  | .input => Polynomial.X
  | .add p q => p.polynomial + q.polynomial
  | .mul p q => p.polynomial * q.polynomial
  | .pow p n => p.polynomial ^ n

theorem Expression.polynomial_eval (p : Expression) (s : ℕ) :
    p.polynomial.eval s = p.eval s := by
  induction p with
  | constant c => simp [polynomial, eval]
  | input => simp [polynomial, eval]
  | add p q hp hq => simp [polynomial, eval, hp, hq]
  | mul p q hp hq => simp [polynomial, eval, hp, hq]
  | pow p n hp => simp [polynomial, eval, hp]

theorem Expression.monotone (p : Expression) : Monotone p.eval := by
  intro s t h
  induction p with
  | constant c => exact le_rfl
  | input => exact h
  | add p q hp hq => exact Nat.add_le_add hp hq
  | mul p q hp hq => exact Nat.mul_le_mul hp hq
  | pow p n hp => exact Nat.pow_le_pow_left hp n

def Expression.substitute : Expression → Expression → Expression
  | .constant c, _ => .constant c
  | .input, q => q
  | .add p r, q => .add (p.substitute q) (r.substitute q)
  | .mul p r, q => .mul (p.substitute q) (r.substitute q)
  | .pow p n, q => .pow (p.substitute q) n

theorem Expression.substitute_eval (p q : Expression) (s : ℕ) :
    (p.substitute q).eval s = p.eval (q.eval s) := by
  induction p with
  | constant c => rfl
  | input => rfl
  | add p r hp hr => simp [substitute, eval, hp, hr]
  | mul p r hp hr => simp [substitute, eval, hp, hr]
  | pow p n hp => simp [substitute, eval, hp]

/-- Cost and output size compose along the computation actually run. -/
theorem bind_bounds {K A B : Type*} (x : Work K A) (f : A → Work K B)
    (sizeA : A → ℕ) (sizeB : B → ℕ)
    (p q r t : Expression) (s : ℕ)
    (hx : x.cost ≤ p.eval s) (hsize : sizeA x.value ≤ q.eval s)
    (hf : ∀ a, (f a).cost ≤ r.eval (sizeA a))
    (hout : ∀ a, sizeB (f a).value ≤ t.eval (sizeA a)) :
    (Work.bind x f).cost ≤ (Expression.add p (r.substitute q)).eval s ∧
      sizeB (Work.bind x f).value ≤ (t.substitute q).eval s := by
  rw [Work.bind_cost, Work.bind_value]
  constructor
  · change x.cost + (f x.value).cost ≤ p.eval s + (r.substitute q).eval s
    rw [Expression.substitute_eval]
    exact Nat.add_le_add hx ((hf _).trans (r.monotone hsize))
  · rw [Expression.substitute_eval]
    exact (hout _).trans (t.monotone hsize)

end Decoupling.HighDim.ArithmeticGrowth
