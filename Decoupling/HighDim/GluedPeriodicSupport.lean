import Decoupling.HighDim.GluedPeriodicStrings

/-!
# Nonzero support of the actual closed string

The full x₃ string remains a nonzero physical Pauli support even when
p divides L₃. Distinct periodic cells, rather than its total coefficient,
are what matter for this assertion.
-/
namespace Decoupling.HighDim.GluedPeriodic
open Torus
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (L : Fin 3 → ℕ)

theorem basis_residue_zero_iff (i : Fin 3) (n : ℕ) (hn : n < L i) :
    (QuotientAddGroup.mk' (RectangularLattice.lattice L)) (n • translationBasis i) = 0 ↔ n = 0 := by
  change (↑(n • translationBasis i) : Translation 3 ⧸ RectangularLattice.lattice L) = 0 ↔ n = 0
  rw [QuotientAddGroup.eq_zero_iff]
  constructor
  · intro h
    have hi := ((RectangularLattice.mem_lattice L _).mp h) i
    have hd : (L i : ℤ) ∣ (n : ℤ) := by simpa [translationBasis] using hi
    have hd' : L i ∣ n := by exact_mod_cast hd
    exact Nat.eq_zero_of_dvd_of_lt hd' hn
  · rintro rfl
    simp

theorem norm_coeff_zero (i : Fin 3) (hi : L i ≠ 0) : (norm K L i).coeff 0 = 1 := by
  classical
  have ht (n : ℕ) (hn : n ∈ Finset.range (L i)) :
      (x K L i ^ n).coeff 0 = if n = 0 then 1 else 0 := by
    rw [x, ← mon_nsmul]
    simp only [mon, periodMap_monomial, AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
      basis_residue_zero_iff L i n (Finset.mem_range.mp hn)]
  simp only [norm, AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl ht]
  simp [Nat.pos_of_ne_zero hi]

theorem baseString_ne_zero (hL : L 2 ≠ 0) : baseString K L ≠ 0 := by
  intro h
  have he := congrArg (fun v : Fin 6 → Ring K L => (v 2).coeff 0) h
  have hn := norm_coeff_zero K L 2 hL
  change (norm K L 2).coeff 0 = 0 at he
  exact one_ne_zero (hn.symm.trans he)

/-- Translation of a nonempty closed string cannot turn it into the zero
physical support: the translating Laurent monomial is a genuine unit. -/
theorem string_ne_zero (hL : L 2 ≠ 0) (a : Translation 3) : string K L a ≠ 0 := by
  intro hz
  have he := congrArg (fun v : Fin 6 → Ring K L => mon K L (-a) • v) hz
  simp only [string, smul_smul, mon_neg_mul, one_smul, smul_zero] at he
  exact baseString_ne_zero K L hL he

theorem string_cycle (a : Translation 3) :
    periodicX (RectangularLattice.lattice L) (Glued.checks K) (string K L a) = 0 := by
  rw [periodicX_formula]
  have h : w K L 2 * (mon K L a * norm K L 2) = 0 := by
    rw [mul_left_comm, w_norm, mul_zero]
  funext i
  fin_cases i <;> simp [string, baseString, h]

end
end Decoupling.HighDim.GluedPeriodic
