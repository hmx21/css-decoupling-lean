import Decoupling.HighDim.ToricHodgeCoordinates
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The ordered cells used in the three-dimensional glued-code example

Source: Section V, equation `eq:glued-example`, manuscript fixed by HD008.
These are explicit enumerations of the actual Koszul cells, in the order
vertex; 1,2,3; 12,13,23; 123. The coordinate boundary matrices below are
proved from the existing signed Koszul differential. No exactness or
profile assertion is made merely by defining these coordinates.
-/

namespace Decoupling.HighDim.Glued

open CategoryTheory Matrix Koszul
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def vertex : Cell 3 0 := OrderEmbedding.ofStrictMono Fin.elim0 (by
  intro i; exact Fin.elim0 i)

def edge (i : Fin 3) : Cell 3 1 := OrderEmbedding.ofStrictMono (fun _ => i) (by
  intro a b hab
  have : a = b := Subsingleton.elim _ _
  subst b
  exact (lt_irrefl _ hab).elim)

def plaquette (i : Fin 3) : Cell 3 2 :=
  OrderEmbedding.ofStrictMono (![![0, 1], ![0, 2], ![1, 2]] i) (by
    fin_cases i <;> decide)

def cube : Cell 3 3 := OrderEmbedding.ofStrictMono id strictMono_id

def vertexEquiv : Fin 1 ≃ Cell 3 0 where
  toFun _ := vertex
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv I := by apply DFunLike.ext; intro i; exact Fin.elim0 i

def edgeEquiv : Fin 3 ≃ Cell 3 1 where
  toFun := edge
  invFun I := I 0
  left_inv _ := rfl
  right_inv I := by apply DFunLike.ext; intro i; fin_cases i; rfl

theorem plaquette_injective : Function.Injective plaquette := by
  intro i j h
  have h0 := DFunLike.congr_fun h 0
  have h1 := DFunLike.congr_fun h 1
  clear h
  fin_cases i <;> fin_cases j <;> simp_all [plaquette]

theorem plaquette_surjective : Function.Surjective plaquette := by
  intro I
  have hlt : I 0 < I 1 := I.strictMono (by decide)
  have h : (I 0 = 0 ∧ I 1 = 1) ∨ (I 0 = 0 ∧ I 1 = 2) ∨
      (I 0 = 1 ∧ I 1 = 2) := by omega
  rcases h with h | h | h
  · refine ⟨0, ?_⟩
    apply DFunLike.ext
    intro j
    fin_cases j
    · exact h.1.symm
    · exact h.2.symm
  · refine ⟨1, ?_⟩
    apply DFunLike.ext
    intro j
    fin_cases j
    · exact h.1.symm
    · exact h.2.symm
  · refine ⟨2, ?_⟩
    apply DFunLike.ext
    intro j
    fin_cases j
    · exact h.1.symm
    · exact h.2.symm

def plaquetteEquiv : Fin 3 ≃ Cell 3 2 :=
  Equiv.ofBijective plaquette ⟨plaquette_injective, plaquette_surjective⟩

theorem cube_unique (I : Cell 3 3) : I = cube := by
  have h01 : I 0 < I 1 := I.strictMono (by decide)
  have h12 : I 1 < I 2 := I.strictMono (by decide)
  apply DFunLike.ext
  intro i
  fin_cases i <;> dsimp [cube] <;> omega

def cubeEquiv : Fin 1 ≃ Cell 3 3 where
  toFun _ := cube
  invFun _ := 0
  left_inv _ := Subsingleton.elim _ _
  right_inv I := (cube_unique I).symm

@[simp] theorem face_edge (i : Fin 3) (j : Fin 1) : face (edge i) j = vertex := by
  apply DFunLike.ext
  intro a
  exact Fin.elim0 a

@[simp] theorem edge_eq_edge (i j : Fin 3) : edge i = edge j ↔ i = j :=
  edgeEquiv.injective.eq_iff

@[simp] theorem plaquette_eq_plaquette (i j : Fin 3) :
    plaquette i = plaquette j ↔ i = j := plaquette_injective.eq_iff

@[simp] theorem face_two (I : Cell 3 2) (j : Fin 2) :
    face I j = edge (I (j.succAbove 0)) := by
  apply DFunLike.ext
  intro a
  fin_cases a
  rfl

@[simp] theorem face_cube (i : Fin 3) : face cube i = plaquette (2 - i) := by
  fin_cases i <;> apply DFunLike.ext <;> intro a <;> fin_cases a <;> rfl

variable (A : Type*) [CommRing A]

/-- Coordinates evaluate on the actual ordered cells. -/
def coordinates {k n : ℕ} (e : Fin n ≃ Cell 3 k) : Term A 3 k ≃ₗ[A] (Fin n → A) :=
  (Finsupp.linearEquivFunOnFinite A A (Cell 3 k)).trans
    (LinearEquiv.piCongrLeft A (fun _ : Cell 3 k => A) e).symm

@[simp] theorem coordinates_apply {k n : ℕ} (e : Fin n ≃ Cell 3 k)
    (v : Term A 3 k) (i : Fin n) : coordinates A e v i = v (e i) := rfl

@[simp] theorem coordinates_symm_single {k n : ℕ} (e : Fin n ≃ Cell 3 k) (i : Fin n) :
    (coordinates A e).symm (Pi.single i 1) = Finsupp.single (e i) 1 := by
  apply (coordinates A e).injective
  rw [LinearEquiv.apply_symm_apply]
  funext j
  change (Pi.single i (1 : A) : Fin n → A) j = Finsupp.single (e i) (1 : A) (e j)
  simp only [Pi.single_apply, Finsupp.single_apply, Equiv.apply_eq_iff_eq, eq_comm]

def firstBoundary (w : Fin 3 → A) : Matrix (Fin 1) (Fin 3) A :=
  ![![w 0, w 1, w 2]]

def secondBoundary (w : Fin 3 → A) : Matrix (Fin 3) (Fin 3) A :=
  ![![-w 1, -w 2, 0], ![w 0, 0, -w 2], ![0, w 0, w 1]]

def thirdBoundary (w : Fin 3 → A) : Matrix (Fin 3) (Fin 1) A :=
  ![![w 2], ![-w 1], ![w 0]]

def coordinateBoundary {k m n : ℕ} (w : Fin 3 → A)
    (e : Fin m ≃ Cell 3 k) (f : Fin n ≃ Cell 3 (k + 1)) : Matrix (Fin m) (Fin n) A :=
  LinearMap.toMatrix' ((coordinates A e).toLinearMap.comp
    ((boundary A w k).hom.comp (coordinates A f).symm.toLinearMap))

theorem coordinateBoundary_apply {k m n : ℕ} (w : Fin 3 → A)
    (e : Fin m ≃ Cell 3 k) (f : Fin n ≃ Cell 3 (k + 1)) (v : Fin n → A) :
    coordinateBoundary A w e f *ᵥ v =
      coordinates A e (boundary A w k ((coordinates A f).symm v)) :=
  LinearMap.toMatrix'_mulVec _ _

theorem coordinateBoundary_entry {k m n : ℕ} (w : Fin 3 → A)
    (e : Fin m ≃ Cell 3 k) (f : Fin n ≃ Cell 3 (k + 1)) (i : Fin m) (j : Fin n) :
    coordinateBoundary A w e f i j =
      ∑ a : Fin (k + 1), if face (f j) a = e i then
        (-1 : A) ^ a.val * w (f j a) else 0 := by
  classical
  have h := congrFun (coordinateBoundary_apply A w e f (Pi.single j 1)) i
  rw [coordinates_symm_single, boundary_basis, coordinates_apply] at h
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply,
    Finsupp.sum_apply, Finsupp.single_apply] using h

theorem firstBoundary_coordinates (w : Fin 3 → A) :
    coordinateBoundary A w vertexEquiv edgeEquiv = firstBoundary A w := by
  ext i j
  rw [coordinateBoundary_entry]
  change (∑ a : Fin 1, if face (edge j) a = vertex then
    (-1 : A) ^ a.val * w (edge j a) else 0) = _
  simp only [face_edge, ite_true, Fin.sum_univ_one, Fin.val_zero, pow_zero, one_mul]
  fin_cases i
  fin_cases j <;> rfl

theorem secondBoundary_coordinates (w : Fin 3 → A) :
    coordinateBoundary A w edgeEquiv plaquetteEquiv = secondBoundary A w := by
  ext i j
  rw [coordinateBoundary_entry]
  change (∑ a : Fin 2, if face (plaquette j) a = edge i then
    (-1 : A) ^ a.val * w (plaquette j a) else 0) = _
  simp only [Fin.sum_univ_two, face_two, edge_eq_edge]
  fin_cases i <;> fin_cases j <;> simp [plaquette, secondBoundary]

theorem thirdBoundary_coordinates (w : Fin 3 → A) :
    coordinateBoundary A w plaquetteEquiv cubeEquiv = thirdBoundary A w := by
  ext i j
  rw [coordinateBoundary_entry]
  change (∑ a : Fin 3, if face cube a = plaquette i then
    (-1 : A) ^ a.val * w (cube a) else 0) = _
  simp only [Fin.sum_univ_three, face_cube, plaquette_eq_plaquette]
  fin_cases i <;> fin_cases j <;> simp [cube, thirdBoundary]

end
end Decoupling.HighDim.Glued
