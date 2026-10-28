import Decoupling.HighDim.MinimalLatticeThreeNative
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Tactic.LinearCombination

/-!
# All optimal planes for the example's single plaquette charge

Source: Section V, HD008. This is the linear algebra and lattice arithmetic
used for the actual example bridge: a nonzero Hom-valued charge only on
the 12 plaquette vanishes on a plane exactly when that plane contains e3.
-/

namespace Decoupling.HighDim.GluedMinimum
open MinimalLattice MinimalLattice.Three
noncomputable section
set_option maxHeartbeats 800000

variable {K : Type*} [Field K] {M : Type*} [AddCommGroup M] [Module K M]

def vertical : V (K := K) := ![0, 0, 1]

theorem pair_span_finrank (u v : V (K := K)) (h : LinearIndependent K ![u, v]) :
    Module.finrank K (Submodule.span K ({u, v} : Set (V (K := K)))) = 2 := by
  have hr : Set.range ![u, v] = ({u, v} : Set (V (K := K))) := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [← hr]
  exact finrank_span_eq_card h

theorem vertical_mem_of_independent_det_zero (u v : V (K := K))
    (hli : LinearIndependent K ![u, v]) (hdet : u 0 * v 1 - u 1 * v 0 = 0) :
    vertical ∈ Submodule.span K ({u, v} : Set (V (K := K))) := by
  have hn : minors u v ≠ 0 := (minors_ne_zero_iff u v).mpr hli
  by_cases h02 : u 0 * v 2 - u 2 * v 0 = 0
  · have h12 : u 1 * v 2 - u 2 * v 1 ≠ 0 := by
      intro hz
      apply hn
      ext k
      fin_cases k <;> simp [minors, hdet, h02, hz]
    apply Submodule.mem_span_pair.mpr
    refine ⟨-v 1 / (u 1 * v 2 - u 2 * v 1), u 1 / (u 1 * v 2 - u 2 * v 1), ?_⟩
    ext k
    fin_cases k
    · change -v 1 / _ * u 0 + u 1 / _ * v 0 = 0
      have hn0 : -v 1 * u 0 + u 1 * v 0 = 0 := by linear_combination -hdet
      calc
        _ = (-v 1 * u 0 + u 1 * v 0) / (u 1 * v 2 - u 2 * v 1) := by ring
        _ = 0 := by rw [hn0, zero_div]
    · change -v 1 / _ * u 1 + u 1 / _ * v 1 = 0
      ring
    · change -v 1 / _ * u 2 + u 1 / _ * v 2 = 1
      calc
        _ = (u 1 * v 2 - u 2 * v 1) / (u 1 * v 2 - u 2 * v 1) := by ring
        _ = 1 := div_self h12
  · apply Submodule.mem_span_pair.mpr
    refine ⟨-v 0 / (u 0 * v 2 - u 2 * v 0), u 0 / (u 0 * v 2 - u 2 * v 0), ?_⟩
    ext k
    fin_cases k
    · change -v 0 / _ * u 0 + u 0 / _ * v 0 = 0
      ring
    · change -v 0 / _ * u 1 + u 0 / _ * v 1 = 0
      have hn0 : -v 0 * u 1 + u 0 * v 1 = 0 := by linear_combination hdet
      calc
        _ = (-v 0 * u 1 + u 0 * v 1) / (u 0 * v 2 - u 2 * v 0) := by ring
        _ = 0 := by rw [hn0, zero_div]
    · change -v 0 / _ * u 2 + u 0 / _ * v 2 = 1
      calc
        _ = (u 0 * v 2 - u 2 * v 0) / (u 0 * v 2 - u 2 * v 0) := by ring
        _ = 1 := div_self h02

theorem det_zero_of_vertical_mem (u v : V (K := K))
    (hz : vertical ∈ Submodule.span K ({u, v} : Set (V (K := K)))) :
    u 0 * v 1 - u 1 * v 0 = 0 := by
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hz
  have h0 := congrFun hab 0
  have h1 := congrFun hab 1
  have h2 := congrFun hab 2
  change a * u 0 + b * v 0 = 0 at h0
  change a * u 1 + b * v 1 = 0 at h1
  change a * u 2 + b * v 2 = 1 at h2
  have ha : a * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination v 1 * h0 - v 0 * h1
  have hb : b * (u 0 * v 1 - u 1 * v 0) = 0 := by linear_combination u 0 * h1 - u 1 * h0
  by_contra hd
  have ha0 := (mul_eq_zero.mp ha).resolve_right hd
  have hb0 := (mul_eq_zero.mp hb).resolve_right hd
  simp [ha0, hb0] at h2

theorem plane_isotropic_iff_contains_vertical (a : M) (ha : a ≠ 0)
    (W : Submodule K (V (K := K))) (hdim : Module.finrank K W = 2) :
    Isotropic (![a, 0, 0] : Fin 3 → M) W ↔ vertical ∈ W := by
  constructor
  · intro hW
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (by omega : 2 ≤ Module.finrank K W)
    have hli : LinearIndependent K (fun i => (v i : V (K := K))) :=
      hv.map' W.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have hp : LinearIndependent K ![(v 0 : V (K := K)), (v 1 : V (K := K))] := by
      convert hli using 1
      ext i
      fin_cases i <;> rfl
    have hdet := hW _ (v 0).property _ (v 1).property
    simp [evaluate, minors, Fin.sum_univ_succ, ha] at hdet
    exact (Submodule.span_le.mpr (by intro x hx; rcases hx with rfl | rfl <;> exact (v _).property))
      (vertical_mem_of_independent_det_zero _ _ hp hdet)
  · intro hz u hu v hv
    have hdet : u 0 * v 1 - u 1 * v 0 = 0 := by
      by_cases hli : LinearIndependent K ![u, v]
      · have hle : Submodule.span K ({u, v} : Set (V (K := K))) ≤ W :=
          Submodule.span_le.mpr (by intro x hx; rcases hx with rfl | rfl <;> assumption)
        have he := Submodule.eq_of_le_of_finrank_eq hle ((pair_span_finrank u v hli).trans hdim.symm)
        exact det_zero_of_vertical_mem u v (he.symm ▸ hz)
      · have hm : minors u v = 0 := by by_contra hne; exact hli ((minors_ne_zero_iff u v).mp hne)
        exact congrFun hm 0
    simp [evaluate, minors, Fin.sum_univ_succ, hdet]

end
end Decoupling.HighDim.GluedMinimum
