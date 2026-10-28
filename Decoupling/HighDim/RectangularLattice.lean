import Decoupling.HighDim.GluedDirectional

/-!
# Actual rectangular period lattices

The periods are positive natural numbers, independently in every
coordinate. The subgroup, inclusion, integer basis and index are proved
from the genuine coordinate residue homomorphism.
-/

namespace Decoupling.HighDim.RectangularLattice

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {D : ℕ} (L : Fin D → ℕ)

def inclusion : Translation D →+ Translation D where
  toFun a i := (L i : ℤ) * a i
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp [mul_add]

def lattice : AddSubgroup (Translation D) := (inclusion L).range

theorem mem_lattice (a : Translation D) : a ∈ lattice L ↔ ∀ i, (L i : ℤ) ∣ a i := by
  constructor
  · rintro ⟨b, rfl⟩ i
    exact ⟨b i, rfl⟩
  · intro h
    choose b hb using h
    exact ⟨b, funext fun i => (hb i).symm⟩

theorem inclusion_injective (hL : ∀ i, L i ≠ 0) : Function.Injective (inclusion L) := by
  intro a b h
  funext i
  exact mul_left_cancel₀ (by exact_mod_cast hL i : (L i : ℤ) ≠ 0) (congrFun h i)

def coordinates (hL : ∀ i, L i ≠ 0) : lattice L ≃+ Translation D :=
  (AddMonoidHom.ofInjective (inclusion_injective L hL)).symm

@[simp] theorem coordinates_symm_coe (hL : ∀ i, L i ≠ 0) (a : Translation D) :
    ((coordinates L hL).symm a : Translation D) = inclusion L a := rfl

def residue : Translation D →+ (∀ i : Fin D, ZMod (L i)) where
  toFun a i := a i
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp

theorem residue_surjective : Function.Surjective (residue L) := by
  intro a
  have h : ∀ i, ∃ b : ℤ, (b : ZMod (L i)) = a i := fun i => ZMod.intCast_surjective (a i)
  choose b hb using h
  exact ⟨b, funext hb⟩

theorem lattice_eq_ker : lattice L = (residue L).ker := by
  ext a
  rw [mem_lattice]
  change (∀ i, (L i : ℤ) ∣ a i) ↔ (fun i => (a i : ZMod (L i))) = 0
  simp only [funext_iff, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]

theorem lattice_index (hL : ∀ i, L i ≠ 0) : (lattice L).index = ∏ i, L i := by
  let : ∀ i, NeZero (L i) := fun i => ⟨hL i⟩
  rw [lattice_eq_ker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top_of_surjective _ (residue_surjective L)]
  simp [Nat.card_eq_fintype_card, Fintype.card_pi]

theorem lattice_finiteIndex (hL : ∀ i, L i ≠ 0) : (lattice L).FiniteIndex where
  index_ne_zero := by rw [lattice_index L hL]; exact Finset.prod_ne_zero_iff.mpr (fun i _ => hL i)

theorem coordinateEmbedding_eq (K : Type) [CommRing K] (hL : ∀ i, L i ≠ 0) :
    ScalingLattice.coordinateEmbedding K (lattice L) (coordinates L hL) =
      KoszulLattice.latticeMap K (inclusion L) := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro a
    change ScalingLattice.coordinateEmbedding K (lattice L) (coordinates L hL) (constant a) =
      KoszulLattice.latticeMap K (inclusion L) (constant a)
    simp only [ScalingLattice.coordinateEmbedding_constant, KoszulLattice.latticeMap_constant]
  · intro a
    change ScalingLattice.coordinateEmbedding K (lattice L) (coordinates L hL) (monomial K a) =
      KoszulLattice.latticeMap K (inclusion L) (monomial K a)
    simp only [ScalingLattice.coordinateEmbedding_monomial, KoszulLattice.latticeMap_monomial,
      coordinates_symm_coe]

end
end Decoupling.HighDim.RectangularLattice
