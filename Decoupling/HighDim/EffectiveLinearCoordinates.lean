import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Exact finite coefficient coordinates for degree-bounded polynomial systems

Source: `drafts/appendix.tex`, C5, coefficient comparison in polynomial rings.
This file proves the finite linear-algebra reduction for an explicitly supplied
box bound. It does not assert that an arbitrary solvable polynomial system has
a solution in that box; the uniform Hermann bound is a separate obligation.
The coefficient matrix is formed from the actual polynomial multiplication map.
-/

namespace Decoupling.HighDim.EffectiveLinear

open MvPolynomial Matrix
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable (K : Type*) [CommRing K] (N : ℕ)

/-- An exponent vector lying in the genuine common coefficient box. -/
def BoxExponent (b : ℕ) := {a : Fin N →₀ ℕ // ∀ i, a i ≤ b}

def boxExponentEquiv (b : ℕ) : BoxExponent N b ≃ (Fin N → Fin (b + 1)) where
  toFun a i := ⟨a.val i, Nat.lt_succ_of_le (a.property i)⟩
  invFun a := ⟨Finsupp.equivFunOnFinite.symm (fun i => (a i).val), by
    intro i
    exact Nat.le_of_lt_succ (a i).isLt⟩
  left_inv a := by apply Subtype.ext; ext i; rfl
  right_inv a := by ext i; rfl

instance (b : ℕ) : Fintype (BoxExponent N b) :=
  Fintype.ofEquiv (Fin N → Fin (b + 1)) (boxExponentEquiv N b).symm

@[simp] theorem card_boxExponent (b : ℕ) :
    Fintype.card (BoxExponent N b) = (b + 1) ^ N := by
  rw [Fintype.card_congr (boxExponentEquiv N b)]
  simp

/-- Actual polynomials, with their actual support bounded coordinatewise. -/
abbrev BoxPolynomial (b : ℕ) := MvPolynomial.restrictDegree (Fin N) K b

def boxBasis (b : ℕ) : Module.Basis (BoxExponent N b) K (BoxPolynomial K N b) :=
  MvPolynomial.basisRestrictSupport K {a : Fin N →₀ ℕ | ∀ i, a i ≤ b}

def boxCoordinates (b : ℕ) : BoxPolynomial K N b ≃ₗ[K] (BoxExponent N b → K) :=
  (boxBasis K N b).equivFun

def vectorCoordinates (n b : ℕ) :
    (Fin n → BoxPolynomial K N b) ≃ₗ[K] ((Fin n × BoxExponent N b) → K) where
  toFun y i := boxCoordinates K N b (y i.1) i.2
  invFun y i := (boxCoordinates K N b).symm (fun a => y (i, a))
  left_inv y := by funext i; exact (boxCoordinates K N b).symm_apply_apply (y i)
  right_inv y := by ext i; exact congrFun ((boxCoordinates K N b).apply_symm_apply
    (fun a => y (i.1, a))) i.2
  map_add' y z := by ext i; exact congrFun ((boxCoordinates K N b).map_add (y i.1) (z i.1)) i.2
  map_smul' a y := by ext i; exact congrFun ((boxCoordinates K N b).map_smul a (y i.1)) i.2

@[simp] theorem card_vectorCoordinates (n b : ℕ) :
    Fintype.card (Fin n × BoxExponent N b) = n * (b + 1) ^ N := by simp

variable {K N} {m n d : ℕ}

/-- Multiplication raises each individual degree by at most the sum of the bounds. -/
theorem mul_mem_box {a b : ℕ} {f g : MvPolynomial (Fin N) K}
    (hf : f ∈ MvPolynomial.restrictDegree (Fin N) K a)
    (hg : g ∈ MvPolynomial.restrictDegree (Fin N) K b) :
    f * g ∈ MvPolynomial.restrictDegree (Fin N) K (a + b) := by
  rw [MvPolynomial.mem_restrictDegree_iff_sup] at hf hg ⊢
  simp only [← MvPolynomial.degreeOf_def] at hf hg ⊢
  intro i
  exact (MvPolynomial.degreeOf_mul_le i f g).trans (Nat.add_le_add (hf i) (hg i))

/-- The actual polynomial matrix product remains in the proved output box. -/
theorem mulVec_mem_box (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (hA : ∀ i j, A i j ∈ MvPolynomial.restrictDegree (Fin N) K d)
    (b : ℕ) (y : Fin n → BoxPolynomial K N b) (i : Fin m) :
    (A *ᵥ (fun j => (y j).val)) i ∈ MvPolynomial.restrictDegree (Fin N) K (d + b) := by
  change (∑ j, A i j * (y j).val) ∈ _
  apply Submodule.sum_mem
  intro j _
  exact mul_mem_box (hA i j) (y j).property

/-- Restrict the actual polynomial matrix action to the finite coefficient spaces. -/
def boundedMul (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (hA : ∀ i j, A i j ∈ MvPolynomial.restrictDegree (Fin N) K d) (b : ℕ) :
    (Fin n → BoxPolynomial K N b) →ₗ[K] (Fin m → BoxPolynomial K N (d + b)) where
  toFun y i := ⟨(A *ᵥ fun j => (y j).val) i, mulVec_mem_box A hA b y i⟩
  map_add' y z := by
    funext i
    apply Subtype.ext
    change (A *ᵥ (fun j => (y j).val + (z j).val)) i = _
    simp only [Matrix.mulVec, dotProduct, mul_add, Finset.sum_add_distrib]
    rfl
  map_smul' a y := by
    funext i
    apply Subtype.ext
    change (A *ᵥ (fun j => a • (y j).val)) i = _
    simp only [Matrix.mulVec, dotProduct, mul_smul_comm, ← Finset.smul_sum]
    rfl

/-- An ordinary finite matrix over K, whose entries are actual coefficient comparisons. -/
def coefficientMatrix (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (hA : ∀ i j, A i j ∈ MvPolynomial.restrictDegree (Fin N) K d) (b : ℕ) :
    Matrix (Fin m × BoxExponent N (d + b)) (Fin n × BoxExponent N b) K :=
  by
  classical
  exact LinearMap.toMatrix' ((vectorCoordinates K N m (d + b)).toLinearMap.comp
    ((boundedMul A hA b).comp (vectorCoordinates K N n b).symm.toLinearMap))

/-- Polynomial matrix multiplication and the finite coefficient matrix agree exactly. -/
theorem coefficientMatrix_mulVec (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (hA : ∀ i j, A i j ∈ MvPolynomial.restrictDegree (Fin N) K d)
    (b : ℕ) (y : Fin n → BoxPolynomial K N b) :
    coefficientMatrix A hA b *ᵥ vectorCoordinates K N n b y =
      vectorCoordinates K N m (d + b) (boundedMul A hA b y) := by
  rw [coefficientMatrix, LinearMap.toMatrix'_mulVec]
  simp

/-- Exact finite reduction, without an unproved assertion that the bound is sufficient. -/
theorem bounded_solution_iff (A : Matrix (Fin m) (Fin n) (MvPolynomial (Fin N) K))
    (hA : ∀ i j, A i j ∈ MvPolynomial.restrictDegree (Fin N) K d)
    (b : ℕ) (v : Fin m → BoxPolynomial K N (d + b)) :
    (∃ y : Fin n → BoxPolynomial K N b,
      A *ᵥ (fun j => (y j).val) = fun i => (v i).val) ↔
    ∃ z : (Fin n × BoxExponent N b) → K,
      coefficientMatrix A hA b *ᵥ z = vectorCoordinates K N m (d + b) v := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨vectorCoordinates K N n b y, ?_⟩
    rw [coefficientMatrix_mulVec]
    congr 1
    funext i
    exact Subtype.ext (congrFun hy i)
  · rintro ⟨z, hz⟩
    let y := (vectorCoordinates K N n b).symm z
    have hzy : vectorCoordinates K N n b y = z :=
      (vectorCoordinates K N n b).apply_symm_apply z
    rw [← hzy, coefficientMatrix_mulVec] at hz
    have he := (vectorCoordinates K N m (d + b)).injective hz
    exact ⟨y, funext fun i => congrArg Subtype.val (congrFun he i)⟩

end
end Decoupling.HighDim.EffectiveLinear
