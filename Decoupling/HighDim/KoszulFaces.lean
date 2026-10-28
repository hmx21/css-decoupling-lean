import Decoupling.HighDim.Laurent
import Mathlib.Order.Fin.Basic
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.Category.ModuleCat.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Ordered cells and weighted faces for the actual Koszul complex

Source: `drafts/main.tex:370–382`, equation `eq:koszul`.
The basis consists of strictly increasing tuples, equivalently ordered
subsets of the coordinate directions. Removing a coordinate is defined
using the actual order embedding that skips that position. Coefficients
are arbitrary elements of a commutative ring; no characteristic assumption
or exactness hypothesis is made.
-/

namespace Decoupling.HighDim.Koszul

open CategoryTheory

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (A : Type*) [CommRing A]

/-- An oriented coordinate `k`-cell, with its directions listed increasingly. -/
abbrev Cell (D k : ℕ) := Fin k ↪o Fin D

instance cellFinite (D k : ℕ) : Finite (Cell D k) :=
  Finite.of_injective (fun I : Cell D k => (I : Fin k → Fin D)) DFunLike.coe_injective

instance cellFintype (D k : ℕ) : Fintype (Cell D k) := Fintype.ofFinite _

/-- The actual free module on the ordered coordinate cells. -/
abbrev Term (D k : ℕ) := Cell D k →₀ A

instance termFree (D k : ℕ) : Module.Free A (Term A D k) := inferInstance

variable {D k : ℕ}

/-- Delete the `i`-th entry while preserving the induced increasing order. -/
def face (I : Cell D (k + 1)) (i : Fin (k + 1)) : Cell D k :=
  (Fin.succAboveOrderEmb i).trans I

@[simp] theorem face_apply (I : Cell D (k + 1)) (i : Fin (k + 1)) (j : Fin k) :
    face I i j = I (i.succAbove j) := rfl

/-- Deleting two directions in the two admissible orders gives the same cell. -/
theorem face_face (I : Cell D (k + 2)) (i : Fin (k + 1)) (j : Fin (k + 2))
    (h : j.val ≤ i.val) :
    face (face I j) i =
      face (face I i.succ) (Fin.castLT j (lt_of_le_of_lt h i.is_lt)) := by
  apply DFunLike.ext
  intro a
  simp only [face_apply]
  apply congrArg I
  have hj : j ≤ i.castSucc := h
  have hp : i.predAbove j = Fin.castLT j (lt_of_le_of_lt h i.is_lt) := by
    rw [Fin.predAbove_of_le_castSucc _ _ hj]
    rfl
  simpa only [Fin.succAbove_of_le_castSucc _ _ hj, hp] using
    (Fin.succAbove_succAbove_succAbove_predAbove j i a).symm

variable (w : Fin D → A)

/-- A weighted face sends `e_I` to `w_(I_i) e_(I\i)`. -/
def weightedFace (k : ℕ) (i : Fin (k + 1)) :
    ModuleCat.of A (Term A D (k + 1)) ⟶ ModuleCat.of A (Term A D k) :=
  ModuleCat.ofHom (Finsupp.linearCombination A
    (fun I : Cell D (k + 1) => Finsupp.single (face I i) (w (I i))))

@[simp] theorem weightedFace_single (i : Fin (k + 1)) (I : Cell D (k + 1)) (a : A) :
    weightedFace A w k i (Finsupp.single I a) =
      Finsupp.single (face I i) (a * w (I i)) := by
  simp [weightedFace, Finsupp.smul_single, smul_eq_mul]

/-- The weighted face identity, proved from actual coordinate deletion and
commutativity of the coefficients. This will imply the alternating square
is zero; it is not an assumed relation. -/
theorem weightedFace_comp (i : Fin (k + 1)) (j : Fin (k + 2)) (h : j.val ≤ i.val) :
    weightedFace A w (k + 1) j ≫ weightedFace A w k i =
      weightedFace A w (k + 1) i.succ ≫
        weightedFace A w k (Fin.castLT j (lt_of_le_of_lt h i.is_lt)) := by
  apply ModuleCat.hom_ext
  apply Finsupp.lhom_ext
  intro I a
  change weightedFace A w k i (weightedFace A w (k + 1) j (Finsupp.single I a)) =
    weightedFace A w k (Fin.castLT j (lt_of_le_of_lt h i.is_lt))
      (weightedFace A w (k + 1) i.succ (Finsupp.single I a))
  simp only [weightedFace, ModuleCat.hom_ofHom, Finsupp.linearCombination_single,
    Finsupp.smul_single, smul_eq_mul, face_face I i j h, face_apply]
  have hj : j ≤ i.castSucc := h
  have hi : (Fin.castLT j (lt_of_le_of_lt h i.is_lt)).castSucc < i.succ := by
    exact h.trans_lt (Nat.lt_succ_self _)
  rw [Fin.succAbove_of_le_castSucc _ _ hj, Fin.succAbove_of_castSucc_lt _ _ hi]
  apply congrArg (Finsupp.single _)
  exact mul_right_comm _ _ _

end

end Decoupling.HighDim.Koszul
