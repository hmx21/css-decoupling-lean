import Decoupling.HighDim.MinimalLattice
import Mathlib.LinearAlgebra.Alternating.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Exact minimization for simultaneous vanishing of alternating forms

Source: the finite-family conclusion of Proposition 1, HD008.
The codomains and positive degrees may vary independently. This is the
arithmetic and multilinear part of the proposition; identifying these
forms with native Ext classes is a separate theorem.
-/

namespace Decoupling.HighDim.MinimalLattice
noncomputable section
attribute [local instance] Classical.propDecidable

variable {p D : ℕ} [Fact p.Prime]
variable {ι : Type*} (degree : ι → ℕ) (Value : ι → Type*)
  [∀ i, AddCommGroup (Value i)] [∀ i, Module (ZMod p) (Value i)]
  (forms : ∀ i, AlternatingMap (ZMod p) (Residue p D) (Value i) (Fin (degree i)))

/-- All arguments lie in the subspace; the values are genuinely vector-valued. -/
def VanishesOn (W : Submodule (ZMod p) (Residue p D)) : Prop :=
  ∀ i, ∀ v : Fin (degree i) → Residue p D, (∀ a, v a ∈ W) → forms i v = 0

theorem vanishesOn_bot (positive : ∀ i, 0 < degree i) :
    VanishesOn degree Value forms ⊥ := by
  intro i v hv
  have h : v = 0 := funext (fun a => (Submodule.mem_bot (ZMod p)).mp (hv a))
  have : Nonempty (Fin (degree i)) := ⟨⟨0, positive i⟩⟩
  rw [h, AlternatingMap.map_zero]

theorem vanishesOn_mono {W U : Submodule (ZMod p) (Residue p D)}
    (h : W ≤ U) (hu : VanishesOn degree Value forms U) :
    VanishesOn degree Value forms W := by
  intro i v hv
  exact hu i v (fun a => h (hv a))

theorem vanishesOn_top_iff :
    VanishesOn degree Value forms ⊤ ↔ ∀ i, forms i = 0 := by
  constructor
  · intro h i
    ext v
    exact h i v (fun _ => Submodule.mem_top)
  · intro h i v _
    simp [h i]

/-- An index prime to p cannot kill any nonzero alternating class. -/
theorem vanishesOn_image_iff_zero_of_not_dvd_index
    (Γ : AddSubgroup (Translation D)) (h : ¬ p ∣ Γ.index) :
    VanishesOn degree Value forms (image p D Γ) ↔ ∀ i, forms i = 0 := by
  rw [image_eq_top_of_not_dvd_index p D Γ h, vanishesOn_top_iff]

theorem exists_vanishing_codim (positive : ∀ i, 0 < degree i) :
    ∃ n : ℕ, ∃ W : Submodule (ZMod p) (Residue p D),
      VanishesOn degree Value forms W ∧ codim p D W = n :=
  ⟨codim p D ⊥, ⊥, vanishesOn_bot degree Value forms positive, rfl⟩

/-- The least codimension is selected from actual subspaces, not postulated. -/
def minimumCodim (positive : ∀ i, 0 < degree i) : ℕ :=
  Nat.find (exists_vanishing_codim degree Value forms positive)

theorem minimumCodim_attained (positive : ∀ i, 0 < degree i) :
    ∃ W : Submodule (ZMod p) (Residue p D),
      VanishesOn degree Value forms W ∧ codim p D W =
        minimumCodim degree Value forms positive :=
  Nat.find_spec (exists_vanishing_codim degree Value forms positive)

theorem minimumCodim_le (positive : ∀ i, 0 < degree i)
    (W : Submodule (ZMod p) (Residue p D)) (hW : VanishesOn degree Value forms W) :
    minimumCodim degree Value forms positive ≤ codim p D W :=
  Nat.find_min' (exists_vanishing_codim degree Value forms positive) ⟨W, hW, rfl⟩

/-- A minimizing subspace gives an actual finite-index lattice attaining p^c. -/
theorem minimumIndex_attained (positive : ∀ i, 0 < degree i) :
    ∃ Γ : AddSubgroup (Translation D), Γ.FiniteIndex ∧
      VanishesOn degree Value forms (image p D Γ) ∧
      Γ.index = p ^ minimumCodim degree Value forms positive := by
  obtain ⟨W, hW, hc⟩ := minimumCodim_attained degree Value forms positive
  refine ⟨preimage p D W, inferInstance, ?_, ?_⟩
  · simpa using hW
  · rw [preimage_index, hc]

/-- Every admissible finite-index lattice satisfies the required lower bound. -/
theorem minimumIndex_le (positive : ∀ i, 0 < degree i)
    (Γ : AddSubgroup (Translation D)) [Γ.FiniteIndex]
    (hΓ : VanishesOn degree Value forms (image p D Γ)) :
    p ^ minimumCodim degree Value forms positive ≤ Γ.index := by
  exact (Nat.pow_le_pow_right (Fact.out : p.Prime).pos
    (minimumCodim_le degree Value forms positive _ hΓ)).trans
      (pow_codim_le_index p D Γ)

/-- Exact minimum, with both attainment and comparison against every candidate. -/
theorem minimumIndex_isLeast (positive : ∀ i, 0 < degree i) :
    IsLeast {n : ℕ | ∃ Γ : AddSubgroup (Translation D), Γ.FiniteIndex ∧
      VanishesOn degree Value forms (image p D Γ) ∧ Γ.index = n}
      (p ^ minimumCodim degree Value forms positive) := by
  refine ⟨minimumIndex_attained degree Value forms positive, ?_⟩
  rintro n ⟨Γ, hfin, hΓ, rfl⟩
  let := hfin
  exact minimumIndex_le degree Value forms positive Γ hΓ

end
end Decoupling.HighDim.MinimalLattice
