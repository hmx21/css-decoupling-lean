import Decoupling.HighDim.GluedMinimumPlanes

/-!
# The complete family of index-p isotropic lattices for a single charge

Index p itself forces the mod-p image to be a plane; this fact is proved
from the actual quotient order, without assuming saturation of a lattice.
-/

namespace Decoupling.HighDim.GluedMinimum
open MinimalLattice MinimalLattice.Three
noncomputable section

variable {p D : ℕ} [Fact p.Prime]

theorem eq_preimage_of_index_prime (Γ : AddSubgroup (Translation D)) (hind : Γ.index = p) :
    Γ = preimage p D (image p D Γ) := by
  apply le_antisymm (le_preimage_image p D Γ)
  intro a ha
  obtain ⟨b, hb, hab⟩ := ha
  have hz : reduction p D (a - b) = 0 := by rw [map_sub, hab, sub_self]
  have hdiv : ∀ i, (p : ℤ) ∣ (a - b) i := fun i =>
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (congrFun hz i)
  choose t ht using hdiv
  have he : a - b = p • t := by
    ext i
    simpa only [Pi.smul_apply, nsmul_eq_mul] using ht i
  have hm : a - b ∈ Γ := by
    rw [he, ← hind]
    exact Γ.nsmul_index_mem t
  simpa only [sub_add_cancel] using Γ.add_mem hm hb

theorem codim_image_of_index_prime (Γ : AddSubgroup (Translation D)) (hind : Γ.index = p) :
    codim p D (image p D Γ) = 1 := by
  apply Nat.pow_right_injective (Fact.out : p.Prime).two_le
  change p ^ codim p D (image p D Γ) = p ^ 1
  rw [← preimage_index, ← eq_preimage_of_index_prime Γ hind, hind, pow_one]

variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M]

/-- Exactly the index-p subgroups whose mod-p images contain the third
coordinate direction annihilate the example's plaquette class. -/
theorem indexPrime_isotropic_iff (a : M) (ha : a ≠ 0)
    (Γ : AddSubgroup (Translation 3)) (hind : Γ.index = p) :
    Isotropic (![a, 0, 0] : Fin 3 → M) (image p 3 Γ) ↔ vertical ∈ image p 3 Γ := by
  apply plane_isotropic_iff_contains_vertical a ha
  have he := codim_add_finrank p 3 (image p 3 Γ)
  rw [codim_image_of_index_prime Γ hind] at he
  change Module.finrank (ZMod p) (image p 3 Γ) = 2
  omega

end
end Decoupling.HighDim.GluedMinimum
