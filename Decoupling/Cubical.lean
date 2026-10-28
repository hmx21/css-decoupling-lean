import Decoupling.ToricWindows

/-!
# Cubical incidence and the two toric windows

A cell orientation is the set of coordinate axes along which it extends.
Removing an axis gives two opposite faces: the face at the base cell and its
translate by that axis. Over F₂ both have coefficient one. This independent
incidence definition recovers the manuscript's cyclic Koszul matrices.
-/

namespace Decoupling.Cubical

open Matrix PhysicalKoszul

noncomputable section

abbrev Orientation := Finset (Fin 3)

/-- The boundary of an elementary cubical cell at the origin, recorded in
Laurent chains indexed by face orientations. -/
def boundary (s : Orientation) : Orientation → R :=
  ∑ i ∈ s, Pi.single (s.erase i) (monomial (translationBasis i) + 1)

def vertex (_ : Fin 1) : Orientation := ∅
def edge (i : Fin 3) : Orientation := {i}

/-- The face order is yz, zx, xy, as in the manuscript. -/
def face (i : Fin 3) : Orientation := ![{1, 2}, {2, 0}, {0, 1}] i
def cube (_ : Fin 1) : Orientation := {0, 1, 2}

def boundary₁ : Matrix (Fin 1) (Fin 3) R := fun i j => boundary (edge j) (vertex i)
def boundary₂ : Matrix (Fin 3) (Fin 3) R := fun i j => boundary (face j) (edge i)
def boundary₃ : Matrix (Fin 3) (Fin 1) R := fun i j => boundary (cube j) (face i)

/-- The two endpoint vertices of each edge give ∂₁=(u,v,w). -/
theorem boundary₁_eq : boundary₁ = partial₁ := by
  funext i j
  fin_cases i
  fin_cases j <;> simp [boundary₁, boundary, vertex, edge, partial₁, Koszul.d₁,
    u, v, w, x, y, z, laurent_sub_eq_add]

/-- The four edges of each oriented face give precisely the cyclic ∂₂. -/
theorem boundary₂_eq : boundary₂ = partial₂ := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [boundary₂, boundary, face, edge, partial₂, Koszul.d₂,
      u, v, w, x, y, z, laurent_sub_eq_add, Pi.single_apply]

/-- The six faces of a cube give ∂₃=(u,v,w)ᵀ in yz,zx,xy order. -/
theorem boundary₃_eq : boundary₃ = partial₃ := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp +decide [boundary₃, boundary, cube, face, partial₃, Koszul.d₃,
      u, v, w, x, y, z, laurent_sub_eq_add, Pi.single_apply]

/-- A translated boundary has the same incidence pattern shifted to its cell. -/
def translatedBoundary (s : Orientation) (a : Translation) : Orientation → R :=
  fun t => monomial a * boundary s t

theorem translatedBoundary_formula (s t : Orientation) (a : Translation) :
    translatedBoundary s a t =
      ∑ i ∈ s, if s.erase i = t then
        monomial (a + translationBasis i) + monomial a else 0 := by
  simp [translatedBoundary, boundary, Finset.mul_sum, Pi.single_apply,
    mul_ite, mul_add, monomial_mul, eq_comm]

end
end Decoupling.Cubical
