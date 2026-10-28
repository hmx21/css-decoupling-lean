import Decoupling.HighDim.GluedTopology
import Decoupling.HighDim.RectangularLattice
import Decoupling.HighDim.TorusPeriodic
import Mathlib.Algebra.Ring.GeomSum

/-!
# Literal periodic operators of the glued example

Source: HD010, main Section IV.B, “The torus”. All operators below live
in the actual quotient group algebra of the rectangular period lattice.
The checks are the literal periodicized matrices, not a logical-count model.
-/

namespace Decoupling.HighDim.GluedPeriodic
open Matrix Torus
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (L : Fin 3 → ℕ)

abbrev Ring := PeriodRing K (RectangularLattice.lattice L)

def mon (a : Translation 3) : Ring K L :=
  periodMap (RectangularLattice.lattice L) (monomial K a)

def x (i : Fin 3) : Ring K L := mon K L (translationBasis i)
def w (i : Fin 3) : Ring K L := x K L i - 1

@[simp] theorem mon_zero : mon K L 0 = 1 := by simp [mon]
@[simp] theorem mon_add (a b : Translation 3) :
    mon K L (a + b) = mon K L a * mon K L b := by simp [mon]
@[simp] theorem mon_neg_mul (a : Translation 3) : mon K L (-a) * mon K L a = 1 := by
  rw [← mon_add]; simp

theorem mon_nsmul (a : Translation 3) (n : ℕ) : mon K L (n • a) = mon K L a ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [succ_nsmul, mon_add, ih, pow_succ]

@[simp] theorem x_period (i : Fin 3) : x K L i ^ L i = 1 := by
  rw [x, ← mon_nsmul]
  apply periodMap_period
  apply (RectangularLattice.mem_lattice L _).mpr
  intro j
  by_cases h : j = i
  · subst j
    simp [translationBasis]
  · simp [translationBasis, h]

def norm (i : Fin 3) : Ring K L := ∑ n ∈ Finset.range (L i), x K L i ^ n

@[simp] theorem w_norm (i : Fin 3) : w K L i * norm K L i = 0 := by
  rw [w, norm, mul_geom_sum, x_period, sub_self]

@[simp] theorem norm_w (i : Fin 3) : norm K L i * w K L i = 0 := by
  rw [mul_comm, w_norm]

/-- Sum of all charge coefficients on the actual periodic lattice. -/
def total : Ring K L →+* K :=
  AddMonoidAlgebra.liftNCRingHom (.id _)
    (1 : Multiplicative ((Translation 3) ⧸ RectangularLattice.lattice L) →* K)
    (by intro a b; exact Commute.one_right _)

@[simp] theorem total_mon (a : Translation 3) : total K L (mon K L a) = 1 := by
  simp [mon, periodMap_monomial, total]

@[simp] theorem total_x (i : Fin 3) : total K L (x K L i) = 1 := total_mon K L _
@[simp] theorem total_w (i : Fin 3) : total K L (w K L i) = 0 := by simp [w]
@[simp] theorem total_norm (i : Fin 3) : total K L (norm K L i) = (L i : K) := by
  simp [norm]

theorem periodicX_formula (v : Fin 6 → Ring K L) :
    periodicX (RectangularLattice.lattice L) (Glued.checks K) v =
      ![w K L 0 * v 0 + w K L 1 * v 1 + w K L 2 * v 2 - v 3,
        -w K L 1 * v 3 - w K L 2 * v 4,
        w K L 0 * v 3 - w K L 2 * v 5,
        w K L 0 * v 4 + w K L 1 * v 5] := by
  funext i
  fin_cases i <;>
    simp [periodicX, Glued.checks, Glued.xChecks, Matrix.mulVec, dotProduct,
      Fin.sum_univ_succ, difference, w, x, mon, coordinate] <;> ring

theorem periodicZ_formula (v : Fin 4 → Ring K L) :
    periodicZ (RectangularLattice.lattice L) (Glued.checks K) v =
      ![-w K L 1 * v 0 - w K L 2 * v 1,
        w K L 0 * v 0 - w K L 2 * v 2,
        w K L 0 * v 1 + w K L 1 * v 2 + v 3,
        w K L 2 * v 3, -w K L 1 * v 3, w K L 0 * v 3] := by
  funext i
  fin_cases i <;>
    simp [periodicZ, Glued.checks_Z_dagger, Glued.zGenerators, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ, difference, w, x, mon, coordinate] <;> ring

/-- Full x₁x₂ plane of plaquette qudits at x₃=0. -/
def plane : Fin 6 → Ring K L := ![0, 0, 0, norm K L 0 * norm K L 1, 0, 0]

/-- Arbitrary edge-supported Z operator, including every possible string correction. -/
def edges (u : Fin 3 → Ring K L) : Fin 6 → Ring K L := ![u 0, u 1, u 2, 0, 0, 0]

theorem plane_syndrome :
    periodicX (RectangularLattice.lattice L) (Glued.checks K) (plane K L) =
      ![-(norm K L 0 * norm K L 1), 0, 0, 0] := by
  rw [periodicX_formula]
  have h0 : w K L 0 * (norm K L 0 * norm K L 1) = 0 := by
    rw [← mul_assoc, w_norm, zero_mul]
  have h1 : w K L 1 * (norm K L 0 * norm K L 1) = 0 := by
    rw [mul_left_comm, w_norm, mul_zero]
  funext i
  fin_cases i <;> simp [plane, h0, h1]

theorem edges_total_charge (u : Fin 3 → Ring K L) :
    total K L (periodicX (RectangularLattice.lattice L) (Glued.checks K) (edges K L u) 0) = 0 := by
  rw [periodicX_formula]
  simp [edges]

/-- The charge remains −L₁L₂ after any edge/string correction. -/
theorem corrected_plane_total_charge (u : Fin 3 → Ring K L) :
    total K L (periodicX (RectangularLattice.lattice L) (Glued.checks K)
      (plane K L + edges K L u) 0) = -((L 0 : K) * (L 1 : K)) := by
  rw [map_add, Pi.add_apply, map_add, plane_syndrome, edges_total_charge]
  simp

end
end Decoupling.HighDim.GluedPeriodic
