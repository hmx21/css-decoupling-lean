import Decoupling.HighDim.LatticeBasis
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.Dimension.RankNullity
import Mathlib.LinearAlgebra.Dimension.DivisionRing
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Mod-p images and exact indices of retained lattices

Source: Proposition 1 and Appendix B.2 of the HD008 manuscript.
This module proves the lattice arithmetic independently of Ext: every
subspace has an actual inverse-image integer lattice of index p^codim,
and its index divides that of every lattice with the same mod-p image.
The native Ext restriction criterion is connected in subsequent modules.
-/

namespace Decoupling.HighDim.MinimalLattice
noncomputable section

variable (p D : ℕ) [Fact p.Prime]

abbrev Residue := Fin D → ZMod p

/-- Coordinatewise reduction of the genuine integer translation lattice. -/
def reduction : Translation D →+ Residue p D where
  toFun a i := a i
  map_zero' := by ext i; simp
  map_add' a b := by ext i; simp

theorem reduction_surjective : Function.Surjective (reduction p D) := by
  intro a
  refine ⟨fun i => (a i).val, ?_⟩
  ext i
  simp [reduction]

/-- The image is a vector subspace because the coefficient field is prime. -/
def image (Γ : AddSubgroup (Translation D)) : Submodule (ZMod p) (Residue p D) :=
  AddSubgroup.toZModSubmodule p (Γ.map (reduction p D))

@[simp] theorem mem_image (Γ : AddSubgroup (Translation D)) (a : Residue p D) :
    a ∈ image p D Γ ↔ ∃ b ∈ Γ, reduction p D b = a := Iff.rfl

/-- Pulling back a vector subspace gives a full-rank actual integer lattice. -/
def preimage (W : Submodule (ZMod p) (Residue p D)) : AddSubgroup (Translation D) :=
  W.toAddSubgroup.comap (reduction p D)

@[simp] theorem mem_preimage (W : Submodule (ZMod p) (Residue p D)) (a : Translation D) :
    a ∈ preimage p D W ↔ reduction p D a ∈ W := Iff.rfl

@[simp] theorem image_preimage (W : Submodule (ZMod p) (Residue p D)) :
    image p D (preimage p D W) = W := by
  ext a
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact hb
  · intro ha
    obtain ⟨b, rfl⟩ := reduction_surjective p D a
    exact ⟨b, ha, rfl⟩

theorem le_preimage_image (Γ : AddSubgroup (Translation D)) :
    Γ ≤ preimage p D (image p D Γ) := by
  intro a ha
  exact ⟨a, ha, rfl⟩

/-- Codimension, defined as the dimension of the actual quotient vector space. -/
def codim (W : Submodule (ZMod p) (Residue p D)) : ℕ :=
  Module.finrank (ZMod p) (Residue p D ⧸ W)

theorem codim_add_finrank (W : Submodule (ZMod p) (Residue p D)) :
    codim p D W + Module.finrank (ZMod p) W = D := by
  simpa [codim, Residue] using W.finrank_quotient_add_finrank

theorem codim_le (W : Submodule (ZMod p) (Residue p D)) : codim p D W ≤ D := by
  have := codim_add_finrank p D W
  omega

theorem preimage_index (W : Submodule (ZMod p) (Residue p D)) :
    (preimage p D W).index = p ^ codim p D W := by
  rw [preimage, AddSubgroup.index_comap_of_surjective W.toAddSubgroup
    (reduction_surjective p D)]
  change Nat.card (Residue p D ⧸ W) = p ^ codim p D W
  rw [Module.natCard_eq_pow_finrank (K := ZMod p), Nat.card_zmod]
  rfl

instance preimage_finiteIndex (W : Submodule (ZMod p) (Residue p D)) :
    (preimage p D W).FiniteIndex where
  index_ne_zero := by
    rw [preimage_index]
    exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero

theorem pow_codim_dvd_index (Γ : AddSubgroup (Translation D)) :
    p ^ codim p D (image p D Γ) ∣ Γ.index := by
  rw [← preimage_index]
  exact AddSubgroup.index_dvd_of_le (le_preimage_image p D Γ)

theorem pow_codim_le_index (Γ : AddSubgroup (Translation D)) [Γ.FiniteIndex] :
    p ^ codim p D (image p D Γ) ≤ Γ.index :=
  Nat.le_of_dvd (Nat.pos_of_ne_zero AddSubgroup.FiniteIndex.index_ne_zero)
    (pow_codim_dvd_index p D Γ)

@[simp] theorem codim_eq_zero_iff (W : Submodule (ZMod p) (Residue p D)) :
    codim p D W = 0 ↔ W = ⊤ := by
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    simpa [h, Residue] using codim_add_finrank p D W
  · rintro rfl
    have h := codim_add_finrank p D (⊤ : Submodule (ZMod p) (Residue p D))
    simp [Residue] at h
    omega

/-- Prime-to-p coarse-graining has full mod-p image. -/
theorem image_eq_top_of_not_dvd_index (Γ : AddSubgroup (Translation D))
    (h : ¬ p ∣ Γ.index) : image p D Γ = ⊤ := by
  apply (codim_eq_zero_iff p D _).mp
  by_contra hzero
  have hn : 1 ≤ codim p D (image p D Γ) := Nat.one_le_iff_ne_zero.mpr hzero
  exact h (by simpa using (pow_dvd_pow p hn).trans (pow_codim_dvd_index p D Γ))

end
end Decoupling.HighDim.MinimalLattice
