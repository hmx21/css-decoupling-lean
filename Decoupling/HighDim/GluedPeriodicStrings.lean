import Decoupling.HighDim.GluedPeriodicOperators
import Decoupling.HighDim.Augmentation

/-!
# Parallel closed strings and literal periodic stabilizers

Source: HD010 Section IV.B, “The torus”. The submodule here is the
range of the actual periodic Z-check matrix. Every equivalence of strings
is proved by membership in that range, with no appeal to dimension counts.
-/

namespace Decoupling.HighDim.GluedPeriodic
open Matrix Torus
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (L : Fin 3 → ℕ)

def stabilizers : Submodule (Ring K L) (Fin 6 → Ring K L) :=
  LinearMap.range (((Glued.zGenerators K).map
    (periodMap (RectangularLattice.lattice L))).mulVecLin)

theorem mem_stabilizers (v : Fin 6 → Ring K L) : v ∈ stabilizers K L ↔
    ∃ u : Fin 4 → Ring K L,
      periodicZ (RectangularLattice.lattice L) (Glued.checks K) u = v := by
  simp only [stabilizers, LinearMap.mem_range, periodicZ, Glued.checks_Z_dagger,
    LinearMap.coe_restrictScalars]

/-- The closed x₃ string at x₁=x₂=0 in actual periodic qudit coordinates. -/
def baseString : Fin 6 → Ring K L := ![0, 0, norm K L 2, 0, 0, 0]

def string (a : Translation 3) : Fin 6 → Ring K L := mon K L a • baseString K L

/-- The product of the two transverse period norms is literally the sum
over all L₁L₂ parallel closed strings in one rectangular fundamental cell. -/
theorem sum_parallel_strings :
    (∑ a ∈ Finset.range (L 0), ∑ b ∈ Finset.range (L 1),
      string K L (a • translationBasis 0 + b • translationBasis 1)) =
        (norm K L 0 * norm K L 1) • baseString K L := by
  simp only [string, mon_add, mon_nsmul, norm, x, Finset.sum_mul,
    Finset.mul_sum, Finset.sum_smul]
  exact Finset.sum_comm

def stringCoefficients : Ring K L →ₗ[Ring K L] (Fin 6 → Ring K L) :=
  (LinearMap.id : Ring K L →ₗ[Ring K L] Ring K L).smulRight (baseString K L)

/-- The coefficients that produce actual stabilizer strings form an ideal. -/
def stringIdeal : Ideal (Ring K L) := (stabilizers K L).comap (stringCoefficients K L)

theorem w_mem_stringIdeal (i : Fin 3) : w K L i ∈ stringIdeal K L := by
  change w K L i • baseString K L ∈ stabilizers K L
  rw [mem_stabilizers]
  fin_cases i
  · refine ⟨![0, norm K L 2, 0, 0], ?_⟩
    rw [periodicZ_formula]
    funext j
    fin_cases j <;> simp [baseString]
  · refine ⟨![0, 0, norm K L 2, 0], ?_⟩
    rw [periodicZ_formula]
    funext j
    fin_cases j <;> simp [baseString]
  · refine ⟨0, ?_⟩
    rw [map_zero]
    funext j
    fin_cases j <;> simp [baseString]

/-- All integer translates of the closed string differ by actual Z stabilizers.
This also covers negative coordinates, not just chosen residue representatives. -/
theorem string_sub_base_mem (a : Translation 3) :
    string K L a - baseString K L ∈ stabilizers K L := by
  have hI : augmentationIdeal K 3 ≤
      Ideal.comap (periodMap (RectangularLattice.lattice L)) (stringIdeal K L) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change periodMap (RectangularLattice.lattice L) (difference K i) ∈ stringIdeal K L
    simpa only [difference, map_sub, map_one, coordinate, mon, x, w] using
      w_mem_stringIdeal K L i
  have h := hI (monomial_sub_one_mem_augmentationIdeal (K := K) a)
  change (stringCoefficients K L)
    (periodMap (RectangularLattice.lattice L) (monomial K a - 1)) ∈ stabilizers K L at h
  simpa [stringCoefficients, string, mon, sub_smul] using h

theorem parallel_strings_equivalent (a b : Translation 3) :
    string K L a - string K L b ∈ stabilizers K L := by
  convert (stabilizers K L).sub_mem (string_sub_base_mem K L a)
    (string_sub_base_mem K L b) using 1
  abel

theorem baseString_cycle :
    periodicX (RectangularLattice.lattice L) (Glued.checks K) (baseString K L) = 0 := by
  rw [periodicX_formula]
  funext i
  fin_cases i <;> simp [baseString]

/-- Multiplying all cube checks leaves precisely the sum of the parallel
x₃ strings. The plaquette components cancel by their real periodic boundaries. -/
theorem all_cubes_boundary :
    periodicZ (RectangularLattice.lattice L) (Glued.checks K)
      ![0, 0, 0, norm K L 0 * norm K L 1 * norm K L 2] =
      (norm K L 0 * norm K L 1) • baseString K L := by
  rw [periodicZ_formula]
  have h (i : Fin 3) : w K L i * (norm K L 0 * norm K L 1 * norm K L 2) = 0 := by
    fin_cases i
    · change w K L 0 * (norm K L 0 * norm K L 1 * norm K L 2) = 0
      calc
        _ = (w K L 0 * norm K L 0) * norm K L 1 * norm K L 2 := by ring
        _ = 0 := by simp only [w_norm, zero_mul]
    · change w K L 1 * (norm K L 0 * norm K L 1 * norm K L 2) = 0
      calc
        _ = norm K L 0 * (w K L 1 * norm K L 1) * norm K L 2 := by ring
        _ = 0 := by simp only [w_norm, mul_zero, zero_mul]
    · change w K L 2 * (norm K L 0 * norm K L 1 * norm K L 2) = 0
      calc
        _ = (norm K L 0 * norm K L 1) * (w K L 2 * norm K L 2) := by ring
        _ = 0 := by simp only [w_norm, mul_zero]
  funext i
  fin_cases i <;> simp [baseString, h]

/-- A period norm differs from its number of cells by a coefficient
that produces an actual string stabilizer. -/
theorem norm_sub_card_mem_stringIdeal (i : Fin 3) :
    norm K L i - (L i : Ring K L) ∈ stringIdeal K L := by
  have hp (n : ℕ) : x K L i ^ n - 1 ∈ stringIdeal K L := by
    induction n with
    | zero => simp
    | succ n ih =>
      convert (stringIdeal K L).add_mem
        ((stringIdeal K L).mul_mem_left (x K L i) ih) (w_mem_stringIdeal K L i) using 1
      simp only [w, pow_succ]
      ring
  have hs := (stringIdeal K L).sum_mem (fun n (_ : n ∈ Finset.range (L i)) => hp n)
  simpa only [norm, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one] using hs

/-- The product of the transverse periods times a single closed string
is an actual Z stabilizer. No invertibility of that product is needed yet. -/
theorem multiple_baseString_mem :
    (L 0 * L 1) • baseString K L ∈ stabilizers K L := by
  have hn : norm K L 0 * norm K L 1 - (L 0 * L 1 : ℕ) ∈ stringIdeal K L := by
    convert (stringIdeal K L).add_mem
      ((stringIdeal K L).mul_mem_left (norm K L 0) (norm_sub_card_mem_stringIdeal K L 1))
      ((stringIdeal K L).mul_mem_right (L 1 : Ring K L)
        (norm_sub_card_mem_stringIdeal K L 0)) using 1
    simp only [Nat.cast_mul]
    ring
  have hdiff : (norm K L 0 * norm K L 1) • baseString K L -
      (L 0 * L 1) • baseString K L ∈ stabilizers K L := by
    change stringCoefficients K L
      (norm K L 0 * norm K L 1 - (L 0 * L 1 : ℕ)) ∈ stabilizers K L at hn
    simpa only [stringCoefficients, LinearMap.smulRight_apply, LinearMap.id_apply,
      sub_smul, Nat.cast_smul_eq_nsmul] using hn
  have htotal : (norm K L 0 * norm K L 1) • baseString K L ∈ stabilizers K L :=
    (mem_stabilizers K L _).mpr ⟨_, all_cubes_boundary K L⟩
  convert (stabilizers K L).sub_mem htotal hdiff using 1
  abel

end
end Decoupling.HighDim.GluedPeriodic
