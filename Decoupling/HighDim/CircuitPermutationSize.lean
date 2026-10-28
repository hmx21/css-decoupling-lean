import Decoupling.HighDim.CircuitSize

/-! # HD012 counted onsite permutation and actual stabilization word -/
namespace Decoupling.HighDim.Circuit
open Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι : Type*} [DecidableEq ι]

theorem swapFactorsAux_length : ∀ (l : List ι) (σ : Equiv.Perm ι)
    (h : ∀ {x}, σ x ≠ x → x ∈ l), (Equiv.Perm.swapFactorsAux l σ h).val.length ≤ l.length := by
  intro l
  induction l with
  | nil => intro σ h; simp [Equiv.Perm.swapFactorsAux]
  | cons a l ih =>
    intro σ h
    simp only [Equiv.Perm.swapFactorsAux]
    split
    · rename_i ha
      exact (ih σ (by
        intro x hx
        exact List.mem_of_ne_of_mem (fun he : x = a => by simp [he, ha.symm] at hx) (h hx))).trans
        (Nat.le_succ _)
    · apply Nat.succ_le_succ
      apply ih
      intro x hx
      have hh := Equiv.Perm.ne_and_ne_of_swap_mul_apply_ne_self hx
      exact List.mem_of_ne_of_mem hh.2 (h hh.1)

variable {K : Type*} [CommRing K] {D : ℕ} [Fintype ι]

theorem word_of_swap_factors (l : List (Equiv.Perm ι)) (h : ∀ σ ∈ l, σ.IsSwap) :
    ∃ c : List (SWAP ι), swapAction (K := K) (D := D) c = permMatrix l.prod ∧ c.length = l.length := by
  induction l with
  | nil => exact ⟨[], rfl, rfl⟩
  | cons σ l ih =>
    obtain ⟨i, j, hij, rfl⟩ := h σ (by simp)
    obtain ⟨c, hc, hl⟩ := ih (fun τ hτ => h τ (by simp [hτ]))
    refine ⟨⟨i, j, hij⟩ :: c, ?_, by simp [hl]⟩
    rw [swapAction_cons, List.prod_cons, permMatrix_mul, hc]
    rfl

/-- The actual onsite permutation needs no more than one SWAP layer per
species. No assumption that arbitrary permutations are depth one is used. -/
theorem permutation_compilation_size (σ : Equiv.Perm ι) :
    ∃ c : List (SWAP ι), swapAction (K := K) (D := D) c = permMatrix σ ∧
      c.length ≤ Fintype.card ι := by
  let h : ∀ {x}, σ x ≠ x → x ∈ (Finset.univ : Finset ι).toList := by
    intro x _
    simp
  let l := Equiv.Perm.swapFactorsAux (Finset.univ : Finset ι).toList σ h
  obtain ⟨c, hc, hl⟩ := word_of_swap_factors (K := K) (D := D) l.val l.property.2
  refine ⟨c, ?_, ?_⟩
  · rw [hc, l.property.1]
  · rw [hl]
    simpa only [Finset.length_toList, Finset.card_univ] using
      swapFactorsAux_length (Finset.univ : Finset ι).toList σ h

variable {U V : Type*} [Fintype U] [Fintype V] [DecidableEq U] [DecidableEq V]

omit [DecidableEq U] [DecidableEq V] in
@[simp] theorem supportSize_neg (g : Matrix U V (Laurent K D)) : supportSize (-g) = supportSize g := by
  simp [supportSize]

/-- The same actual SUM/SWAP word realizes Θ on Z and its inverse dagger
on X, with an explicit support-and-rank length bound. -/
theorem theta_circuit_size (f : Matrix V U (Laurent K D)) (g : Matrix U V (Laurent K D))
    (e : (U ⊕ V) ≃ (V ⊕ U)) :
    ∃ c : List (Layer K D (V ⊕ U)),
      wordZ c = (Stabilization.theta f g).submatrix id e.symm ∧
      wordX c = dagger ((Stabilization.theta g f).submatrix e.symm id) ∧
      c.length ≤ supportSize f + supportSize g + Fintype.card U + Fintype.card V := by
  obtain ⟨a, ha, hla⟩ := two_shear_z_compilation_size (-g) f
  obtain ⟨b, hb, hlb⟩ := permutation_compilation_size (K := K) (D := D)
    (e.symm.trans (Equiv.sumComm U V))
  let c := a.map Layer.sum ++ b.map (Layer.swap (K := K) (D := D))
  have hz : wordZ c = (Stabilization.theta f g).submatrix id e.symm := by
    rw [theta_reindexed]
    change wordZ (a.map Layer.sum ++ b.map Layer.swap) = _
    rw [wordZ_append, wordZ_sum, wordZ_swap, ha, hb]
  have hi : (Stabilization.theta f g).submatrix id e.symm *
      (Stabilization.theta g f).submatrix e.symm id = 1 := by
    rw [Matrix.submatrix_mul_equiv, Stabilization.theta_mul_reverse, Matrix.submatrix_id_id]
  refine ⟨c, hz, wordX_eq_dagger_inverse c _ _ hz hi, ?_⟩
  simp only [c, List.length_append, List.length_map]
  rw [supportSize_neg] at hla
  simp only [Fintype.card_sum] at hlb
  omega

end
end Decoupling.HighDim.Circuit
