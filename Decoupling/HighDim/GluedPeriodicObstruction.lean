import Decoupling.HighDim.GluedPeriodicSupport
import Decoupling.HighDim.GluedPeriodicCount

/-!
# The two explicit periodic obstructions in the glued code

Source: HD010 Section IV.B. A plane has uncancellable total charge when
p does not divide L₁L₂, and the closed x₃ string is an actual stabilizer.
These are matrix kernel/range statements, separate from the exact 6/4 count.
-/

namespace Decoupling.HighDim.GluedPeriodic
open Torus
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (p : ℕ) [Fact p.Prime] (L : Fin 3 → ℕ)

theorem transverse_cast_ne_zero (h : ¬p ∣ L 0 * L 1) :
    ((L 0 * L 1 : ℕ) : ZMod p) ≠ 0 := by
  exact fun hz => h ((ZMod.natCast_eq_zero_iff _ _).mp hz)

/-- No operator supported only on edges can cancel the full plane's charge. -/
theorem corrected_plane_not_cycle (h : ¬p ∣ L 0 * L 1)
    (u : Fin 3 → Ring (ZMod p) L) :
    periodicX (RectangularLattice.lattice L) (Glued.checks (ZMod p))
      (plane (ZMod p) L + edges (ZMod p) L u) ≠ 0 := by
  intro hz
  have hc := corrected_plane_total_charge (ZMod p) L u
  rw [hz, Pi.zero_apply, map_zero] at hc
  have hn : ((L 0 : ZMod p) * (L 1 : ZMod p)) = 0 := neg_eq_zero.mp hc.symm
  exact transverse_cast_ne_zero p L h (by simpa only [Nat.cast_mul] using hn)

/-- Inverting the nonzero transverse area turns the actual multiple-string
stabilizer into a stabilizer supported on a single closed string. -/
theorem baseString_mem_stabilizers (h : ¬p ∣ L 0 * L 1) :
    baseString (ZMod p) L ∈ stabilizers (ZMod p) L := by
  have hn := transverse_cast_ne_zero p L h
  have hm := multiple_baseString_mem (ZMod p) L
  rw [← Nat.cast_smul_eq_nsmul (ZMod p)] at hm
  have hi := ((stabilizers (ZMod p) L).restrictScalars (ZMod p)).smul_mem
    (((L 0 * L 1 : ℕ) : ZMod p)⁻¹) hm
  change (((L 0 * L 1 : ℕ) : ZMod p)⁻¹) •
    (((L 0 * L 1 : ℕ) : ZMod p) • baseString (ZMod p) L) ∈ stabilizers (ZMod p) L at hi
  simpa only [smul_smul, inv_mul_cancel₀ hn, one_smul] using hi

/-- Every integer translate is also the image of actual periodic checks. -/
theorem string_mem_stabilizers (h : ¬p ∣ L 0 * L 1) (a : Translation 3) :
    string (ZMod p) L a ∈ stabilizers (ZMod p) L := by
  exact (stabilizers (ZMod p) L).smul_mem _ (baseString_mem_stabilizers p L h)

/-- A direct witness in the original four types of periodic Z checks. -/
theorem exists_string_check_product (h : ¬p ∣ L 0 * L 1) (a : Translation 3) :
    ∃ z : Fin 4 → Ring (ZMod p) L,
      periodicZ (RectangularLattice.lattice L) (Glued.checks (ZMod p)) z =
        string (ZMod p) L a :=
  (mem_stabilizers (ZMod p) L _).mp (string_mem_stabilizers p L h a)

/-- A genuinely nonzero closed string is trivial in the actual logical
quotient. This remains valid when p divides the longitudinal period L₃. -/
theorem nonzero_string_stabilizer (hL : L 2 ≠ 0) (h : ¬p ∣ L 0 * L 1)
    (a : Translation 3) :
    string (ZMod p) L a ≠ 0 ∧
      ∃ z : Fin 4 → Ring (ZMod p) L,
        periodicZ (RectangularLattice.lattice L) (Glued.checks (ZMod p)) z =
          string (ZMod p) L a :=
  ⟨string_ne_zero (ZMod p) L hL a, exists_string_check_product p L h a⟩

/-- The exact physical quotient count together with the two concrete
operator statements, for all positive rectangular periods and every prime. -/
theorem nondivisible_torus (hL : ∀ i, L i ≠ 0) (h : ¬p ∣ L 0 * L 1) :
    logicalQudits (RectangularLattice.lattice L) (Glued.checks (ZMod p))
        (Glued.topological (ZMod p)) = 4 ∧
      (∀ u : Fin 3 → Ring (ZMod p) L,
        periodicX (RectangularLattice.lattice L) (Glued.checks (ZMod p))
          (plane (ZMod p) L + edges (ZMod p) L u) ≠ 0) ∧
      (∀ a : Translation 3, ∃ z : Fin 4 → Ring (ZMod p) L,
        periodicZ (RectangularLattice.lattice L) (Glued.checks (ZMod p)) z =
          string (ZMod p) L a) := by
  refine ⟨?_, corrected_plane_not_cycle p L h, exists_string_check_product p L h⟩
  simpa only [ite_eq_right h] using Glued.rectangular_logicalQudits p L hL

end
end Decoupling.HighDim.GluedPeriodic
