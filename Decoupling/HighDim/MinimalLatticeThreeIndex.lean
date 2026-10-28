import Decoupling.HighDim.MinimalLatticeThree
import Decoupling.HighDim.MinimalLatticeRelative

/-!
# The exact three-dimensional 1 / p / p² classification

Source: the final sentence of Corollary 2, HD008. This proves the
minimum for the actual vector-valued determinant table. Connecting the
table to the canonical native CSS gluing class is done upstream.
-/

namespace Decoupling.HighDim.MinimalLattice.Three
noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

variable {p : ℕ} [Fact p.Prime] {M : Type*} [AddCommGroup M] [Module (ZMod p) M]
  (values : Fin 3 → M)

def minCodim : ℕ := minimumCodim (fun _ : Unit => 2) (fun _ => M)
  (fun _ => form (K := ZMod p) values) (fun _ => by decide)

theorem vanishesOn_iff_isotropic (W : Submodule (ZMod p) (Residue p 3)) :
    VanishesOn (fun _ : Unit => 2) (fun _ => M) (fun _ => form (K := ZMod p) values) W ↔
      Isotropic values W := by
  constructor
  · intro h u hu v hv
    exact h () ![u, v] (by intro i; fin_cases i <;> assumption)
  · intro h _ v hv
    exact h (v 0) (hv 0) (v 1) (hv 1)

theorem minCodim_attained :
    ∃ W : Submodule (ZMod p) (Residue p 3), Isotropic values W ∧
      codim p 3 W = minCodim (p := p) values := by
  obtain ⟨W, hW, hc⟩ := minimumCodim_attained (fun _ : Unit => 2) (fun _ => M)
    (fun _ => form (K := ZMod p) values) (fun _ => by decide)
  exact ⟨W, (vanishesOn_iff_isotropic values W).mp hW, hc⟩

theorem minCodim_le_of_isotropic (W : Submodule (ZMod p) (Residue p 3))
    (hW : Isotropic values W) : minCodim (p := p) values ≤ codim p 3 W :=
  minimumCodim_le (fun _ : Unit => 2) (fun _ => M) (fun _ => form (K := ZMod p) values)
    (fun _ => by decide) W ((vanishesOn_iff_isotropic values W).mpr hW)

theorem minCodim_zero_iff : minCodim (p := p) values = 0 ↔ ∀ i, values i = 0 := by
  constructor
  · intro h
    obtain ⟨W, hW, hc⟩ := minCodim_attained (p := p) values
    have hw : W = ⊤ := (codim_eq_zero_iff p 3 W).mp (hc.trans h)
    exact (isotropic_top_iff values).mp (hw ▸ hW)
  · intro h
    have he : codim p 3 (⊤ : Submodule (ZMod p) (Residue p 3)) = 0 :=
      (codim_eq_zero_iff p 3 _).mpr rfl
    have hl := minCodim_le_of_isotropic (p := p) values ⊤
      ((isotropic_top_iff (K := ZMod p) values).mpr h)
    omega

theorem minCodim_le_two : minCodim (p := p) values ≤ 2 := by
  let u : Residue p 3 := ![1, 0, 0]
  let W := Submodule.span (ZMod p) ({u} : Set (Residue p 3))
  have hu : u ≠ 0 := by intro h; have := congrFun h 0; simp [u] at this
  have hw : Module.finrank (ZMod p) W = 1 := finrank_span_singleton hu
  have hc : codim p 3 W = 2 := by have := codim_add_finrank p 3 W; omega
  exact hc ▸ minCodim_le_of_isotropic values W (span_singleton_isotropic values u)

theorem minCodim_eq_one (hdep : ¬ LinearIndependent (ZMod p) values)
    (hnz : ¬ ∀ i, values i = 0) : minCodim (p := p) values = 1 := by
  obtain ⟨W, hdim, hW⟩ := (exists_isotropic_plane_iff values).mpr hdep
  have hc : codim p 3 W = 1 := by
    have he := codim_add_finrank p 3 W
    change Module.finrank (ZMod p) W = 2 at hdim
    rw [hdim] at he
    omega
  have hle := minCodim_le_of_isotropic values W hW
  have hne : minCodim (p := p) values ≠ 0 := mt (minCodim_zero_iff (p := p) values).mp hnz
  omega

theorem minCodim_eq_two (hi : LinearIndependent (ZMod p) values) : minCodim (p := p) values = 2 := by
  obtain ⟨W, hW, hc⟩ := minCodim_attained (p := p) values
  have hd := isotropic_finrank_le_one values hi W hW
  have he := codim_add_finrank p 3 W
  have hl := minCodim_le_two (p := p) values
  change Module.finrank (ZMod p) W ≤ 1 at hd
  omega

/-- The paper's explicit case distinction, for arbitrary vector-valued coefficients. -/
theorem minCodim_classification : minCodim (p := p) values =
    if ∀ i, values i = 0 then 0 else
      if LinearIndependent (ZMod p) values then 2 else 1 := by
  split_ifs with hzero hind
  · exact (minCodim_zero_iff (p := p) values).mpr hzero
  · exact minCodim_eq_two values hind
  · exact minCodim_eq_one values hind hzero

/-- The exact minimal lattice index, with no assumed minimizing lattice. -/
theorem minimumIndex_classification :
    IsLeast {n : ℕ | ∃ Γ : AddSubgroup (Translation 3), Γ.FiniteIndex ∧
      Isotropic values (image p 3 Γ) ∧ Γ.index = n}
      (if ∀ i, values i = 0 then 1 else
        if LinearIndependent (ZMod p) values then p ^ 2 else p) := by
  have h := minimumIndex_isLeast (fun _ : Unit => 2) (fun _ => M)
    (fun _ => form (K := ZMod p) values) (fun _ => by decide)
  simp only [vanishesOn_iff_isotropic] at h
  change IsLeast _ (p ^ minCodim (p := p) values) at h
  rw [minCodim_classification] at h
  split_ifs at h ⊢ <;> simpa using h

/-- The same classification relative to any actual retained lattice, including skew Λ. -/
theorem relativeMinimumIndex_classification (Λ : AddSubgroup (Translation 3))
    [Λ.FiniteIndex] (e : Λ ≃+ Translation 3) :
    IsLeast {n : ℕ | ∃ Γ : AddSubgroup (Translation 3), Γ ≤ Λ ∧ Γ.FiniteIndex ∧
      Isotropic values (image p 3 (coordinateSubgroup Λ e Γ)) ∧ Γ.relIndex Λ = n}
      (if ∀ i, values i = 0 then 1 else
        if LinearIndependent (ZMod p) values then p ^ 2 else p) := by
  have h := relativeMinimum_isLeast Λ e (fun _ : Unit => 2) (fun _ => M)
    (fun _ => form (K := ZMod p) values) (fun _ => by decide)
  simp only [vanishesOn_iff_isotropic] at h
  change IsLeast _ (p ^ minCodim (p := p) values) at h
  rw [minCodim_classification] at h
  split_ifs at h ⊢ <;> simpa using h

/-- In particular a single nonzero plaquette coefficient needs exactly one p-direction. -/
theorem minimumIndex_single_coefficient (a : M) (ha : a ≠ 0) :
    IsLeast {n : ℕ | ∃ Γ : AddSubgroup (Translation 3), Γ.FiniteIndex ∧
      Isotropic (![a, 0, 0] : Fin 3 → M) (image p 3 Γ) ∧ Γ.index = n} p := by
  have hz : ¬ ∀ i, (![a, 0, 0] : Fin 3 → M) i = 0 := by
    intro h
    exact ha (h 0)
  have hi : ¬ LinearIndependent (ZMod p) (![a, 0, 0] : Fin 3 → M) := by
    intro h
    exact h.ne_zero 1 rfl
  simpa only [hz, hi, ↓reduceIte] using
    minimumIndex_classification (p := p) (![a, 0, 0] : Fin 3 → M)

end
end Decoupling.HighDim.MinimalLattice.Three
