import Decoupling.HighDim.Laurent
import Mathlib.Data.Matrix.Basis
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Weighted SUM layers on the integer lattice

Source: `drafts/main.tex`, Section IV.C. A layer consists of actual disjoint
pairs of lattice sites and applies `(a,b) ↦ (a,b + λ*a)` on each pair.
Its finite-support X labels transform by `I + λ x^a E_target,control`;
its Z labels transform by `I - λ x^(-a) E_control,target`. The coefficient
formulas identify the Laurent maps with the cellwise local transformations.
Weights may lie in any commutative ring; in particular this includes every
prime field and retains the signs at odd characteristic.

These are algebraic configuration and Pauli-label semantics. Complex Hilbert
space unitaries and their conjugation action are not claimed by this module.
-/

noncomputable section

namespace Decoupling.HighDim.Circuit

open Matrix

variable {K : Type*} [CommRing K] {D : ℕ}
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- One translation-invariant layer of weighted SUM gates between distinct species. -/
structure SUM (K : Type*) (D : ℕ) (ι : Type*) where
  control : ι
  target : ι
  displacement : Translation D
  weight : K
  distinct : control ≠ target

namespace SUM

variable (g : SUM K D ι)

def source (n : Translation D) : ι × Translation D := (g.control, n)
def destination (n : Translation D) : ι × Translation D :=
  (g.target, n + g.displacement)

omit [CommRing K] [Fintype ι] [DecidableEq ι] in
theorem distinct_sites (n : Translation D) : g.source n ≠ g.destination n :=
  fun h => g.distinct (congrArg Prod.fst h)

omit [CommRing K] [Fintype ι] [DecidableEq ι] in
/-- Different members of the same layer have no shared physical site. -/
theorem disjoint_gates {n m : Translation D} (hne : n ≠ m) :
    g.source n ≠ g.source m ∧ g.source n ≠ g.destination m ∧
    g.destination n ≠ g.source m ∧ g.destination n ≠ g.destination m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fun h => hne (congrArg Prod.snd h)
  · exact fun h => g.distinct (congrArg Prod.fst h)
  · exact fun h => g.distinct (congrArg Prod.fst h).symm
  · exact fun h => hne (add_right_cancel (congrArg Prod.snd h))

/-- Inverting a weighted SUM negates its weight. -/
def inverse : SUM K D ι := { g with weight := -g.weight }

/-- The actual local action on the two site labels. -/
def localAction (a b : K) : K × K := (a, b + g.weight * a)

omit [Fintype ι] [DecidableEq ι] in
theorem local_inverse (a b : K) :
    g.inverse.localAction (g.localAction a b).1 (g.localAction a b).2 = (a, b) := by
  simp [localAction, inverse]

def xMatrix : Matrix ι ι (Laurent K D) :=
  1 + Matrix.single g.target g.control (AddMonoidAlgebra.single g.displacement g.weight)

omit [Fintype ι] in
theorem inverse_xMatrix : g.inverse.xMatrix =
    1 - Matrix.single g.target g.control
      (AddMonoidAlgebra.single g.displacement g.weight) := by
  simp [xMatrix, inverse, sub_eq_add_neg, Matrix.single_neg]

theorem xMatrix_mul_inverse : g.xMatrix * g.inverse.xMatrix = 1 := by
  have hs : Matrix.single g.target g.control
      (AddMonoidAlgebra.single g.displacement g.weight : Laurent K D) *
      Matrix.single g.target g.control
      (AddMonoidAlgebra.single g.displacement g.weight) = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _ g.distinct _
  rw [inverse_xMatrix]
  unfold xMatrix
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hs,
    sub_zero, sub_add_cancel]

omit [Fintype ι] [DecidableEq ι] in
@[simp] theorem inverse_inverse : g.inverse.inverse = g := by
  cases g
  simp [inverse]

theorem xMatrix_inverse :
    g.xMatrix * g.inverse.xMatrix = 1 ∧ g.inverse.xMatrix * g.xMatrix = 1 :=
  ⟨g.xMatrix_mul_inverse, by simpa using g.inverse.xMatrix_mul_inverse⟩

/-- Cellwise X-label action obtained by applying local SUM to each disjoint pair. -/
def xConfig (p : ι → Translation D → K) (i : ι) (n : Translation D) : K :=
  p i n + if i = g.target then g.weight * p g.control (n - g.displacement) else 0

theorem x_support (p : ι → Laurent K D) (i : ι) (n : Translation D) :
    ((g.xMatrix *ᵥ p) i).coeff n = g.xConfig (fun j => (p j).coeff) i n := by
  simp only [xMatrix, Matrix.add_mulVec, Matrix.one_mulVec, Pi.add_apply,
    Matrix.single_mulVec, AddMonoidAlgebra.coeff_add, xConfig]
  by_cases hi : i = g.target
  · subst i
    simp [sub_eq_add_neg, add_comm]
  · simp [hi]

theorem x_mulVec (p : ι → Laurent K D) (i : ι) :
    (g.xMatrix *ᵥ p) i = p i + if i = g.target then
      AddMonoidAlgebra.single g.displacement g.weight * p g.control else 0 := by
  simp [xMatrix, Matrix.add_mulVec, Matrix.single_mulVec, Function.update_apply]

/-- Inverse dagger, not dagger, is essential away from characteristic two. -/
def zMatrix : Matrix ι ι (Laurent K D) := dagger g.inverse.xMatrix

omit [Fintype ι] in
theorem dagger_single {i j : ι} (r : Laurent K D) :
    dagger (Matrix.single i j r) = Matrix.single j i (bar r) := by
  funext a b
  by_cases h : i = b ∧ j = a <;> simp [dagger, and_comm, h]

omit [Fintype ι] in
theorem zMatrix_formula : g.zMatrix =
    1 - Matrix.single g.control g.target
      (AddMonoidAlgebra.single (-g.displacement) g.weight) := by
  simp [zMatrix, inverse_xMatrix, dagger_single, bar, translationNeg]

/-- Cellwise contragredient action on Z labels. -/
def zConfig (p : ι → Translation D → K) (i : ι) (n : Translation D) : K :=
  p i n - if i = g.control then g.weight * p g.target (n + g.displacement) else 0

omit [Fintype ι] in
/-- Restricting the global X-label layer to one pair recovers the actual
two-site SUM formula. Species not targeted by the layer are unchanged. -/
theorem xConfig_pair (p : ι → Translation D → K) (n : Translation D) :
    (g.xConfig p g.control n, g.xConfig p g.target (n + g.displacement)) =
      g.localAction (p g.control n) (p g.target (n + g.displacement)) := by
  simp [xConfig, localAction, g.distinct]

omit [Fintype ι] in
/-- On that same pair the Z labels transform by the signed inverse transpose. -/
theorem zConfig_pair (p : ι → Translation D → K) (n : Translation D) :
    (g.zConfig p g.control n, g.zConfig p g.target (n + g.displacement)) =
      (p g.control n - g.weight * p g.target (n + g.displacement),
        p g.target (n + g.displacement)) := by
  simp [zConfig, Ne.symm g.distinct]

omit [Fintype ι] in
theorem xConfig_untouched (p : ι → Translation D → K) (i : ι)
    (hi : i ≠ g.target) (n : Translation D) : g.xConfig p i n = p i n := by
  simp [xConfig, hi]

omit [Fintype ι] in
theorem zConfig_untouched (p : ι → Translation D → K) (i : ι)
    (hi : i ≠ g.control) (n : Translation D) : g.zConfig p i n = p i n := by
  simp [zConfig, hi]

theorem z_support (p : ι → Laurent K D) (i : ι) (n : Translation D) :
    ((g.zMatrix *ᵥ p) i).coeff n = g.zConfig (fun j => (p j).coeff) i n := by
  rw [zMatrix_formula]
  simp only [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply,
    Matrix.single_mulVec, AddMonoidAlgebra.coeff_sub, zConfig]
  by_cases hi : i = g.control
  · subst i
    simp [add_comm]
  · simp [hi]

omit [Fintype ι] [DecidableEq ι] in
/-- Local X/Z labels preserve the bilinear Pauli exponent pairing. -/
theorem local_pairing (x₁ x₂ z₁ z₂ : K) :
    x₁ * (z₁ - g.weight * z₂) + (x₂ + g.weight * x₁) * z₂ =
      x₁ * z₁ + x₂ * z₂ := by ring

/-- The infinite translation pairing is preserved, including all shifts. -/
theorem preserves_pairing : dagger g.xMatrix * g.zMatrix = 1 := by
  rw [zMatrix, ← dagger_mul, g.xMatrix_inverse.2, dagger_one]

/-- Reverse direction and displacement and negate weight to exchange X and Z actions. -/
def dual : SUM K D ι where
  control := g.target
  target := g.control
  displacement := -g.displacement
  weight := -g.weight
  distinct := Ne.symm g.distinct

omit [Fintype ι] in
theorem dual_xMatrix : g.dual.xMatrix = g.zMatrix := by
  rw [zMatrix_formula]
  simp [xMatrix, dual, sub_eq_add_neg, Matrix.single_neg]

omit [Fintype ι] in
theorem dual_zMatrix : g.dual.zMatrix = g.xMatrix := by
  rw [zMatrix_formula]
  simp [xMatrix, dual, sub_eq_add_neg, Matrix.single_neg]

def relabel {κ : Type*} (e : ι ≃ κ) : SUM K D κ where
  control := e g.control
  target := e g.target
  displacement := g.displacement
  weight := g.weight
  distinct := fun h => g.distinct (e.injective h)

omit [Fintype ι] in
theorem relabel_xMatrix {κ : Type*} [DecidableEq κ] (e : ι ≃ κ) :
    (g.relabel e).xMatrix = g.xMatrix.submatrix e.symm e.symm := by
  simp [xMatrix, relabel, Matrix.submatrix_add]

omit [CommRing K] [Fintype ι] [DecidableEq ι] in
/-- Translation carries each local gate to another member of the same layer. -/
theorem translate_sites (n b : Translation D) :
    g.source (n + b) = (g.control, (g.source n).2 + b) ∧
    g.destination (n + b) = (g.target, (g.destination n).2 + b) := by
  simp [source, destination, add_right_comm]

def translateConfig (b : Translation D) (p : ι → Translation D → K)
    (i : ι) (n : Translation D) : K := p i (n - b)

omit [Fintype ι] in
theorem x_translation_covariant (b : Translation D) (p : ι → Translation D → K) :
    g.xConfig (translateConfig b p) = translateConfig b (g.xConfig p) := by
  funext i n
  simp only [xConfig, translateConfig]
  congr 2
  congr 1
  congr 1
  abel

omit [Fintype ι] in
theorem z_translation_covariant (b : Translation D) (p : ι → Translation D → K) :
    g.zConfig (translateConfig b p) = translateConfig b (g.zConfig p) := by
  funext i n
  simp only [zConfig, translateConfig]
  congr 2
  congr 1
  congr 1
  abel

end SUM

/-- Every Laurent polynomial is the finite sum of its weighted monomials. -/
theorem sum_weighted_monomials (f : Laurent K D) :
    (f.coeff.support.toList.map (fun a => AddMonoidAlgebra.single a (f.coeff a))).sum = f := by
  rw [Finset.sum_map_toList]
  exact AddMonoidAlgebra.sum_coeff_single f

/-- The last listed layer acts first. -/
def xAction (c : List (SUM K D ι)) : Matrix ι ι (Laurent K D) :=
  (c.map SUM.xMatrix).prod
def zAction (c : List (SUM K D ι)) : Matrix ι ι (Laurent K D) :=
  (c.map SUM.zMatrix).prod

@[simp] theorem xAction_nil : xAction ([] : List (SUM K D ι)) = 1 := rfl
@[simp] theorem zAction_nil : zAction ([] : List (SUM K D ι)) = 1 := rfl
@[simp] theorem xAction_cons (g : SUM K D ι) (c : List (SUM K D ι)) :
    xAction (g :: c) = g.xMatrix * xAction c := rfl
@[simp] theorem zAction_cons (g : SUM K D ι) (c : List (SUM K D ι)) :
    zAction (g :: c) = g.zMatrix * zAction c := rfl

theorem xAction_append (c d : List (SUM K D ι)) :
    xAction (c ++ d) = xAction c * xAction d := by simp [xAction]
theorem zAction_append (c d : List (SUM K D ι)) :
    zAction (c ++ d) = zAction c * zAction d := by simp [zAction]

theorem circuit_preserves_pairing (c : List (SUM K D ι)) :
    dagger (xAction c) * zAction c = 1 := by
  induction c with
  | nil => simp
  | cons g c ih =>
    simp only [xAction_cons, zAction_cons, dagger_mul]
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (dagger g.xMatrix),
      g.preserves_pairing, Matrix.one_mul, ih]

theorem xAction_eq_dagger_inverse (c : List (SUM K D ι))
    (A B : Matrix ι ι (Laurent K D)) (hZ : zAction c = A) (hAB : A * B = 1) :
    xAction c = dagger B := by
  have h : dagger (xAction c) = B := by
    calc
      dagger (xAction c) = dagger (xAction c) * (A * B) := by rw [hAB, Matrix.mul_one]
      _ = (dagger (xAction c) * A) * B := (Matrix.mul_assoc _ _ _).symm
      _ = B := by rw [← hZ, circuit_preserves_pairing, Matrix.one_mul]
  simpa only [dagger_dagger] using congrArg dagger h

/-- Both reverse order and inverse local gates are necessary for inversion. -/
def inverseWord (c : List (SUM K D ι)) : List (SUM K D ι) := c.reverse.map SUM.inverse

theorem xAction_inverseWord (c : List (SUM K D ι)) :
    xAction c * xAction (inverseWord c) = 1 := by
  induction c with
  | nil => simp [inverseWord]
  | cons g c ih =>
    simp only [inverseWord, List.reverse_cons, List.map_append, List.map_cons,
      List.map_nil, xAction_append, xAction_cons, xAction_nil, Matrix.mul_one] at *
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc (xAction c), ih,
      Matrix.one_mul, g.xMatrix_mul_inverse]

theorem zAction_dual (c : List (SUM K D ι)) :
    zAction (c.map SUM.dual) = xAction c := by
  induction c with
  | nil => simp
  | cons g c ih => simp [ih, SUM.dual_zMatrix]

theorem xAction_relabel {κ : Type*} [Fintype κ] [DecidableEq κ]
    (c : List (SUM K D ι)) (e : ι ≃ κ) :
    xAction (c.map (fun g => g.relabel e)) = (xAction c).submatrix e.symm e.symm := by
  induction c with
  | nil => simp
  | cons g c ih =>
    simp only [List.map_cons, xAction_cons, SUM.relabel_xMatrix, ih,
      Matrix.submatrix_mul_equiv]

/-- Maximum coordinate displacement in the finite gate list. -/
def rangeBound (c : List (SUM K D ι)) : ℕ :=
  c.foldr (fun g b => max (Finset.univ.sup (fun i => (g.displacement i).natAbs)) b) 0

omit [CommRing K] [Fintype ι] [DecidableEq ι] in
theorem displacement_le_rangeBound (c : List (SUM K D ι)) (g : SUM K D ι)
    (hg : g ∈ c) (i : Fin D) : (g.displacement i).natAbs ≤ rangeBound c := by
  induction c with
  | nil => simp at hg
  | cons h c ih =>
    rcases List.mem_cons.mp hg with rfl | hg
    · exact le_trans (Finset.le_sup (f := fun j => (g.displacement j).natAbs)
        (Finset.mem_univ i)) (Nat.le_max_left _ _)
    · exact le_trans (ih hg) (Nat.le_max_right _ _)

omit [CommRing K] [Fintype ι] [DecidableEq ι] in
theorem finite_depth_range (c : List (SUM K D ι)) :
    ∃ depth range : ℕ, depth = c.length ∧
      ∀ g ∈ c, ∀ i : Fin D, (g.displacement i).natAbs ≤ range :=
  ⟨c.length, rangeBound c, rfl, fun g hg i => displacement_le_rangeBound c g hg i⟩

end Decoupling.HighDim.Circuit
