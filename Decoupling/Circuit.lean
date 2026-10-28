import Decoupling.Laurent
import Decoupling.Stabilization
import Mathlib.Data.Matrix.Basis

/-!
# Translation-invariant CNOT families

Sites are pairs of a species and an integer lattice cell. A family connects
control `(l,n)` to target `(k,n+a)`. Its X action is `I+monomial(a) E_kl`;
its Z action is the inverse dagger. The support formulas below derive the
cellwise action from Laurent multiplication, rather than identifying an
arbitrary elementary matrix with a physical gate by definition.
-/

namespace Decoupling.Circuit

open Matrix

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A depth-one family of equally displaced CNOTs between distinct species. -/
structure CNOT (ι : Type*) where
  control : ι
  target : ι
  displacement : Translation
  distinct : control ≠ target

namespace CNOT

variable (g : CNOT ι)

def source (n : Translation) : ι × Translation := (g.control, n)
def destination (n : Translation) : ι × Translation := (g.target, n + g.displacement)

omit [Fintype ι] [DecidableEq ι] in
/-- No two different members of one family share a physical site. -/
theorem disjoint_gates {n m : Translation} (hne : n ≠ m) :
    g.source n ≠ g.source m ∧ g.source n ≠ g.destination m ∧
    g.destination n ≠ g.source m ∧ g.destination n ≠ g.destination m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun h => hne (congrArg Prod.snd h)
  · exact fun h => g.distinct (congrArg Prod.fst h)
  · exact fun h => g.distinct (congrArg Prod.fst h).symm
  · exact fun h => hne (add_right_cancel (congrArg Prod.snd h))

def xMatrix : Matrix ι ι R :=
  1 + Matrix.single g.target g.control (monomial g.displacement)

/-- Each CNOT family is its own inverse, also over the infinite lattice. -/
theorem xMatrix_involutive : g.xMatrix * g.xMatrix = 1 := by
  have hs : Matrix.single g.target g.control (monomial g.displacement) *
      Matrix.single g.target g.control (monomial g.displacement) = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _ g.distinct _
  simp only [xMatrix, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
    Matrix.mul_one, hs, add_zero]
  rw [add_assoc, Stabilization.matrix_add_self, add_zero]

theorem x_support (p : ι → R) (i : ι) (n : Translation) :
    ((g.xMatrix *ᵥ p) i).coeff n =
      (p i).coeff n + if i = g.target then
        (p g.control).coeff (n - g.displacement) else 0 := by
  simp only [xMatrix, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply,
    Matrix.single_mulVec, AddMonoidAlgebra.coeff_add]
  by_cases hi : i = g.target
  · subst i
    simp [monomial, sub_eq_add_neg, add_comm]
  · simp [hi]

theorem x_mulVec (p : ι → R) (i : ι) :
    (g.xMatrix *ᵥ p) i = p i +
      if i = g.target then monomial g.displacement * p g.control else 0 := by
  simp [xMatrix, Matrix.add_mulVec, Matrix.single_mulVec, Function.update_apply]

def zMatrix : Matrix ι ι R := dagger g.xMatrix

omit [Fintype ι] in
theorem dagger_single {i j : ι} (r : R) :
    dagger (Matrix.single i j r) = Matrix.single j i (bar r) := by
  funext a b
  by_cases h : i = b ∧ j = a <;>
    simp [dagger, and_comm, h]

omit [Fintype ι] in
theorem zMatrix_formula : g.zMatrix =
    1 + Matrix.single g.control g.target (monomial (-g.displacement)) := by
  simp [zMatrix, xMatrix, dagger_single]

/-- Z support propagates from the target to the control with reversed shift. -/
theorem z_support (p : ι → R) (i : ι) (n : Translation) :
    ((g.zMatrix *ᵥ p) i).coeff n =
      (p i).coeff n + if i = g.control then
        (p g.target).coeff (n + g.displacement) else 0 := by
  rw [zMatrix_formula]
  simp only [Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply,
    Matrix.single_mulVec, AddMonoidAlgebra.coeff_add]
  by_cases hi : i = g.control
  · subst i
    simp [monomial, add_comm]
  · simp [hi]

/-- The local X/Z support transformations preserve the Laurent commutator form. -/
theorem preserves_pairing : dagger g.xMatrix * g.zMatrix = 1 := by
  rw [zMatrix, ← dagger_mul, g.xMatrix_involutive, dagger_one]

def dual : CNOT ι where
  control := g.target
  target := g.control
  displacement := -g.displacement
  distinct := Ne.symm g.distinct

omit [Fintype ι] in
theorem dual_xMatrix : g.dual.xMatrix = g.zMatrix := by
  rw [zMatrix_formula]
  rfl

omit [Fintype ι] in
theorem dual_zMatrix : g.dual.zMatrix = g.xMatrix := by
  rw [zMatrix, dual_xMatrix, zMatrix, dagger_dagger]

def relabel {κ : Type*} (e : ι ≃ κ) : CNOT κ where
  control := e g.control
  target := e g.target
  displacement := g.displacement
  distinct := fun h => g.distinct (e.injective h)

omit [Fintype ι] in
theorem relabel_xMatrix {κ : Type*} [DecidableEq κ] (e : ι ≃ κ) :
    (g.relabel e).xMatrix = g.xMatrix.submatrix e.symm e.symm := by
  simp [xMatrix, relabel, Matrix.submatrix_add]

end CNOT

/-- Every Laurent polynomial over F₂ is a finite sum of coefficient-one monomials. -/
theorem sum_monomials (f : R) :
    (f.coeff.support.toList.map monomial).sum = f := by
  rw [Finset.sum_map_toList]
  calc
    ∑ a ∈ f.coeff.support, monomial a = f.coeff.sum AddMonoidAlgebra.single := by
      apply Finset.sum_congr rfl
      intro a ha
      have hn : f.coeff a ≠ 0 := Finsupp.mem_support_iff.mp ha
      have hcases : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide
      have hc : f.coeff a = 1 := (hcases _).resolve_left hn
      simp [hc, monomial]
    _ = f := AddMonoidAlgebra.sum_coeff_single f

/-- Matrix action order: the last listed layer acts first. -/
def xAction (c : List (CNOT ι)) : Matrix ι ι R := (c.map CNOT.xMatrix).prod
def zAction (c : List (CNOT ι)) : Matrix ι ι R := (c.map CNOT.zMatrix).prod

@[simp] theorem xAction_nil : xAction ([] : List (CNOT ι)) = 1 := rfl
@[simp] theorem zAction_nil : zAction ([] : List (CNOT ι)) = 1 := rfl
@[simp] theorem xAction_cons (g : CNOT ι) (c : List (CNOT ι)) :
    xAction (g :: c) = g.xMatrix * xAction c := rfl
@[simp] theorem zAction_cons (g : CNOT ι) (c : List (CNOT ι)) :
    zAction (g :: c) = g.zMatrix * zAction c := rfl

theorem xAction_append (c d : List (CNOT ι)) :
    xAction (c ++ d) = xAction c * xAction d := by
  simp [xAction]

theorem zAction_append (c d : List (CNOT ι)) :
    zAction (c ++ d) = zAction c * zAction d := by
  simp [zAction]

theorem circuit_preserves_pairing (c : List (CNOT ι)) :
    dagger (xAction c) * zAction c = 1 := by
  induction c with
  | nil => simp
  | cons g c ih =>
    simp only [xAction_cons, zAction_cons, dagger_mul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (dagger g.xMatrix),
      g.preserves_pairing, Matrix.one_mul, ih]

/-- Converting a proved Z action to the paper's exact inverse-dagger X action. -/
theorem xAction_eq_dagger_inverse (c : List (CNOT ι)) (A B : Matrix ι ι R)
    (hZ : zAction c = A) (hAB : A * B = 1) : xAction c = dagger B := by
  have h : dagger (xAction c) = B := by
    calc
      dagger (xAction c) = dagger (xAction c) * (A * B) := by rw [hAB, Matrix.mul_one]
      _ = (dagger (xAction c) * A) * B := (Matrix.mul_assoc _ _ _).symm
      _ = B := by rw [← hZ, circuit_preserves_pairing, Matrix.one_mul]
  simpa only [dagger_dagger] using congrArg dagger h

/-- Reversing the layers implements the inverse X action. -/
theorem xAction_reverse (c : List (CNOT ι)) :
    xAction c * xAction c.reverse = 1 := by
  induction c with
  | nil => simp
  | cons g c ih =>
    simp only [List.reverse_cons, xAction_append, xAction_cons, xAction_nil,
      Matrix.mul_one]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (xAction c), ih,
      Matrix.one_mul, g.xMatrix_involutive]

theorem zAction_eq_inverse_dagger (c : List (CNOT ι)) :
    zAction c = dagger (xAction c.reverse) := by
  induction c with
  | nil => simp
  | cons g c ih =>
    simp [List.reverse_cons, xAction_append, ih, CNOT.zMatrix]

theorem zAction_dual (c : List (CNOT ι)) :
    zAction (c.map CNOT.dual) = xAction c := by
  induction c with
  | nil => simp
  | cons g c ih => simp [ih, CNOT.dual_zMatrix]

theorem xAction_relabel {κ : Type*} [Fintype κ] [DecidableEq κ]
    (c : List (CNOT ι)) (e : ι ≃ κ) :
    xAction (c.map (fun g => g.relabel e)) = (xAction c).submatrix e.symm e.symm := by
  induction c with
  | nil => simp
  | cons g c ih =>
    simp only [List.map_cons, xAction_cons, CNOT.relabel_xMatrix, ih,
      Matrix.submatrix_mul_equiv]

/-- Maximum coordinate displacement of any gate in this finite circuit. -/
def rangeBound (c : List (CNOT ι)) : ℕ :=
  c.foldr (fun g b => max (Finset.univ.sup (fun i => (g.displacement i).natAbs)) b) 0

omit [Fintype ι] [DecidableEq ι] in
theorem displacement_le_rangeBound (c : List (CNOT ι)) (g : CNOT ι)
    (hg : g ∈ c) (i : Fin 3) : (g.displacement i).natAbs ≤ rangeBound c := by
  induction c with
  | nil => simp at hg
  | cons h c ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · exact le_trans (Finset.le_sup (f := fun j => (g.displacement j).natAbs)
        (Finset.mem_univ i)) (Nat.le_max_left _ _)
    · exact le_trans (ih hg) (Nat.le_max_right _ _)

omit [Fintype ι] [DecidableEq ι] in
/-- Explicit finite depth and range witnesses depend only on the gate list. -/
theorem finite_depth_range (c : List (CNOT ι)) :
    ∃ depth range : ℕ, depth = c.length ∧
      ∀ g ∈ c, ∀ i : Fin 3, (g.displacement i).natAbs ≤ range :=
  ⟨c.length, rangeBound c, rfl, fun g hg i => displacement_le_rangeBound c g hg i⟩

end
end Decoupling.Circuit
