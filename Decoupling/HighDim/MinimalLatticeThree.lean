import Decoupling.HighDim.MinimalLatticeForms
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Module

/-!
# Vector-valued gluing in dimension three

Source: the three-dimensional classification in Corollary 2, HD008.
The three coefficients may lie in any vector space, in particular
Hom(E_X²,E_X¹); no scalar-valued restriction is made.
-/

namespace Decoupling.HighDim.MinimalLattice.Three
open Matrix
noncomputable section
set_option maxHeartbeats 800000

variable {K : Type*} [Field K]
abbrev V := Fin 3 → K

/-- The ordered minors (01,02,12), with signs retained in all characteristics. -/
def minors (u v : V (K := K)) : V (K := K) :=
  ![u 0 * v 1 - u 1 * v 0, u 0 * v 2 - u 2 * v 0, u 1 * v 2 - u 2 * v 1]

theorem minors_eq_zero_iff_cross (u v : V (K := K)) :
    minors u v = 0 ↔ crossProduct u v = 0 := by
  simp only [minors, cross_apply, cons_eq_zero_iff, zero_empty, and_true, sub_eq_zero]
  tauto

theorem minors_ne_zero_iff (u v : V (K := K)) :
    minors u v ≠ 0 ↔ LinearIndependent K ![u, v] := by
  rw [ne_eq, minors_eq_zero_iff_cross, ← ne_eq, crossProduct_ne_zero_iff_linearIndependent]

/-- Every nonzero bivector in three dimensions is an actual oriented plane. -/
theorem minors_surjective (a : V (K := K)) : ∃ u v : V (K := K), minors u v = a := by
  by_cases h0 : a 0 = 0
  · by_cases h1 : a 1 = 0
    · refine ⟨![0, 1, 0], ![0, 0, a 2], ?_⟩
      ext i
      fin_cases i <;> simp [minors, h0, h1]
    · refine ⟨![1, a 2 / a 1, 0], ![0, 0, a 1], ?_⟩
      ext i
      fin_cases i <;> simp [minors, h0, h1]
  · refine ⟨![1, 0, -a 2 / a 0], ![0, a 0, a 1], ?_⟩
    ext i
    fin_cases i <;> simp [minors, h0]

theorem nonzero_minors_realized (a : V (K := K)) (ha : a ≠ 0) :
    ∃ u v : V (K := K), LinearIndependent K ![u, v] ∧ minors u v = a := by
  obtain ⟨u, v, h⟩ := minors_surjective a
  exact ⟨u, v, (minors_ne_zero_iff u v).mp (h ▸ ha), h⟩

variable {M : Type*} [AddCommGroup M] [Module K M] (values : Fin 3 → M)

/-- Evaluate the coefficient table on the three actual minors. -/
def evaluate (u v : V (K := K)) : M := ∑ i, minors u v i • values i

def bilinear : V (K := K) →ₗ[K] V (K := K) →ₗ[K] M := by
  apply LinearMap.mk₂ K (evaluate values)
  · intro u v w
    simp [evaluate, minors, Fin.sum_univ_succ]
    module
  · intro a u v
    simp [evaluate, minors, Fin.sum_univ_succ]
    module
  · intro u v w
    simp [evaluate, minors, Fin.sum_univ_succ]
    module
  · intro a u v
    simp [evaluate, minors, Fin.sum_univ_succ]
    module

theorem bilinear_apply (u v : V (K := K)) :
    bilinear values u v = evaluate values u v := rfl

@[simp] theorem evaluate_self (u : V (K := K)) : evaluate values u u = 0 := by
  simp [evaluate, minors, Fin.sum_univ_succ, mul_comm]

/-- The table gives an actual alternating map. -/
def form : AlternatingMap K (V (K := K)) M (Fin 2) where
  toFun v := bilinear values (v 0) (v 1)
  map_update_add' v i x y := by
    fin_cases i <;> simp [Function.update]
  map_update_smul' v i a x := by
    fin_cases i <;> simp [Function.update]
  map_eq_zero_of_eq' v i j h hij := by
    fin_cases i <;> fin_cases j <;> simp_all [bilinear_apply]

@[simp] theorem form_pair (u v : V (K := K)) : form values ![u, v] = evaluate values u v := rfl

theorem exists_isotropic_independent_iff :
    (∃ u v : V (K := K), LinearIndependent K ![u, v] ∧ evaluate values u v = 0) ↔
      ¬ LinearIndependent K values := by
  constructor
  · rintro ⟨u, v, huv, hz⟩ hi
    have hm := (minors_ne_zero_iff u v).mpr huv
    apply hm
    exact funext (Fintype.linearIndependent_iff.mp hi (minors u v) hz)
  · intro h
    obtain ⟨a, ha, i, hi⟩ := Fintype.not_linearIndependent_iff.mp h
    have han : a ≠ 0 := fun heq => hi (congrFun heq i)
    obtain ⟨u, v, huv, huv'⟩ := nonzero_minors_realized a han
    refine ⟨u, v, huv, ?_⟩
    simpa [evaluate, huv'] using ha

def Isotropic (W : Submodule K (V (K := K))) : Prop :=
  ∀ u ∈ W, ∀ v ∈ W, evaluate values u v = 0

theorem evaluate_swap (u v : V (K := K)) :
    evaluate values v u = - evaluate values u v := by
  simp [evaluate, minors, Fin.sum_univ_succ]
  module

theorem span_pair_isotropic {u v : V (K := K)} (h : evaluate values u v = 0) :
    Isotropic values (Submodule.span K ({u, v} : Set (V (K := K)))) := by
  intro x hx y hy
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hx
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hy
  change bilinear values (a • u + b • v) (c • u + d • v) = 0
  simp [map_add, map_smul, bilinear_apply, evaluate_swap values u v, h]

theorem span_singleton_isotropic (u : V (K := K)) :
    Isotropic values (Submodule.span K ({u} : Set (V (K := K)))) := by
  intro x hx y hy
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hy
  change bilinear values (a • u) (b • u) = 0
  simp [map_smul, bilinear_apply]

theorem isotropic_top_iff : Isotropic (K := K) values ⊤ ↔ ∀ i, values i = 0 := by
  constructor
  · intro h i
    fin_cases i
    · simpa [evaluate, minors, Fin.sum_univ_succ] using
        h ![1, 0, 0] (Submodule.mem_top) ![0, 1, 0] (Submodule.mem_top)
    · simpa [evaluate, minors, Fin.sum_univ_succ] using
        h ![1, 0, 0] (Submodule.mem_top) ![0, 0, 1] (Submodule.mem_top)
    · simpa [evaluate, minors, Fin.sum_univ_succ] using
        h ![0, 1, 0] (Submodule.mem_top) ![0, 0, 1] (Submodule.mem_top)
  · intro h u _ v _
    simp [evaluate, h]

theorem exists_isotropic_plane_iff :
    (∃ W : Submodule K (V (K := K)), Module.finrank K W = 2 ∧ Isotropic values W) ↔
      ¬ LinearIndependent K values := by
  constructor
  · rintro ⟨W, hdim, hW⟩
    obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (by omega : 2 ≤ Module.finrank K W)
    have hli : LinearIndependent K (fun i => (v i : V (K := K))) :=
      hv.map' W.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
    have hp : LinearIndependent K ![(v 0 : V (K := K)), (v 1 : V (K := K))] := by
      convert hli using 1
      ext i
      fin_cases i <;> rfl
    exact (exists_isotropic_independent_iff values).mp
      ⟨v 0, v 1, hp, hW _ (v 0).property _ (v 1).property⟩
  · intro h
    obtain ⟨u, v, huv, hz⟩ := (exists_isotropic_independent_iff values).mpr h
    refine ⟨Submodule.span K ({u, v} : Set (V (K := K))), ?_, span_pair_isotropic values hz⟩
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
    exact finrank_span_eq_card huv

theorem isotropic_finrank_le_one (h : LinearIndependent K values)
    (W : Submodule K (V (K := K))) (hW : Isotropic values W) : Module.finrank K W ≤ 1 := by
  by_contra hn
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (by omega : 2 ≤ Module.finrank K W)
  have hli : LinearIndependent K (fun i => (v i : V (K := K))) :=
    hv.map' W.subtype (LinearMap.ker_eq_bot.mpr Subtype.val_injective)
  have hp : LinearIndependent K ![(v 0 : V (K := K)), (v 1 : V (K := K))] := by
    convert hli using 1
    ext i
    fin_cases i <;> rfl
  exact (exists_isotropic_independent_iff values).mp
    ⟨v 0, v 1, hp, hW _ (v 0).property _ (v 1).property⟩ h

end
end Decoupling.HighDim.MinimalLattice.Three
