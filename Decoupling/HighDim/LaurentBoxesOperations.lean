import Decoupling.HighDim.LaurentBoxes
import Mathlib.Algebra.MonoidAlgebra.Support

/-! # Actual exponent-box propagation through the construction's matrix formulas -/
namespace Decoupling.HighDim.LaurentBoxes
open Matrix
open scoped Pointwise
noncomputable section
variable {K : Type*} [CommRing K] {D a b h : ℕ}

theorem supported_mono {f : Laurent K D} (hf : Supported f a) (hab : a ≤ b) :
    Supported f b := by
  intro x hx
  rw [mem_box]
  intro i
  have hi := mem_box x |>.mp (hf hx)
  have hii := hi i
  constructor <;> omega

theorem supported_zero : Supported (0 : Laurent K D) h := by
  intro x hx
  simp at hx

theorem supported_one : Supported (1 : Laurent K D) h := by
  intro x hx
  have hx0 : x = 0 := by
    by_contra hn
    have hzero : (1 : Laurent K D).coeff x = 0 := by
      simp [AddMonoidAlgebra.one_def, hn]
    exact Finsupp.mem_support_iff.mp hx hzero
  subst x
  simp [mem_box]

theorem supported_add {f g : Laurent K D} (hf : Supported f h) (hg : Supported g h) :
    Supported (f + g) h := by
  intro x hx
  rcases Finset.mem_union.mp (Finsupp.support_add hx) with hf' | hg'
  · exact hf hf'
  · exact hg hg'

theorem supported_neg {f : Laurent K D} (hf : Supported f h) : Supported (-f) h := by
  intro x hx
  apply hf
  simpa using hx

theorem supported_sub {f g : Laurent K D} (hf : Supported f h) (hg : Supported g h) :
    Supported (f - g) h := by
  rw [sub_eq_add_neg]
  exact supported_add hf (supported_neg hg)

theorem supported_mul {f g : Laurent K D} (hf : Supported f a) (hg : Supported g b) :
    Supported (f * g) (a + b) := by
  classical
  intro x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Finset.mem_add.mp
    (AddMonoidAlgebra.support_coeff_mul_subset f g hx)
  rw [mem_box]
  intro i
  have hyi := mem_box y |>.mp (hf hy) <| i
  have hzi := mem_box z |>.mp (hg hz) <| i
  change -((a + b : ℕ) : ℤ) ≤ y i + z i ∧ y i + z i ≤ ((a + b : ℕ) : ℤ)
  constructor <;> omega

theorem supported_sum {ι : Type*} (s : Finset ι) (f : ι → Laurent K D)
    (hf : ∀ i ∈ s, Supported (f i) h) : Supported (∑ i ∈ s, f i) h := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (supported_zero (K := K) (D := D) (h := h))
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact supported_add (hf i (Finset.mem_insert_self i s))
      (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem supported_bar {f : Laurent K D} (hf : Supported f h) : Supported (bar f) h := by
  intro x hx
  have hn : -x ∈ f.coeff.support := by
    simpa only [Finsupp.mem_support_iff, bar_coeff] using hx
  rw [mem_box]
  intro i
  have hi := mem_box (-x) |>.mp (hf hn) <| i
  change -(h : ℤ) ≤ x i ∧ x i ≤ h
  change -(h : ℤ) ≤ -x i ∧ -x i ≤ h at hi
  constructor <;> omega

variable {U V W : Type*}

theorem matrixSupported_mul [Fintype V] {A : Matrix U V (Laurent K D)} {B : Matrix V W (Laurent K D)}
    (hA : MatrixSupported A a) (hB : MatrixSupported B b) :
    MatrixSupported (A * B) (a + b) := by
  intro i k
  apply supported_sum
  intro j _
  exact supported_mul (hA i j) (hB j k)

theorem matrixSupported_add {A B : Matrix U V (Laurent K D)}
    (hA : MatrixSupported A h) (hB : MatrixSupported B h) :
    MatrixSupported (A + B) h := fun i j => supported_add (hA i j) (hB i j)

theorem matrixSupported_sub {A B : Matrix U V (Laurent K D)}
    (hA : MatrixSupported A h) (hB : MatrixSupported B h) :
    MatrixSupported (A - B) h := fun i j => supported_sub (hA i j) (hB i j)

theorem matrixSupported_dagger {A : Matrix U V (Laurent K D)} (hA : MatrixSupported A h) :
    MatrixSupported (dagger A) h := fun i j => supported_bar (hA j i)

end
end Decoupling.HighDim.LaurentBoxes
