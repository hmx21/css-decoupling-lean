import Decoupling.HighDim.MinimalLatticeRelative
import Decoupling.HighDim.KoszulLatticeRestriction
import Decoupling.HighDim.ScalingLattice

/-!
# Actual subgroup coordinates and the mod-p restriction map

Source: Proposition 1, HD008. The map used by the arbitrary Koszul
comparison is identified with the real subgroup inclusion in any integer
basis. Its linear image is exactly the mod-p image of the subgroup.
-/

namespace Decoupling.HighDim.MinimalLattice
noncomputable section

variable {D : ℕ} (Γ : AddSubgroup (Translation D)) (e : Γ ≃+ Translation D)

def inclusionCoordinates : Translation D →+ Translation D :=
  Γ.subtype.comp e.symm.toAddMonoidHom

@[simp] theorem inclusionCoordinates_apply (a : Translation D) :
    inclusionCoordinates Γ e a = (e.symm a : Translation D) := rfl

theorem latticeMap_eq_coordinateEmbedding (K : Type) [CommRing K] :
    KoszulLattice.latticeMap K (inclusionCoordinates Γ e) =
      ScalingLattice.coordinateEmbedding K Γ e := by
  apply AddMonoidAlgebra.ringHom_ext
  · intro c
    change KoszulLattice.latticeMap K _ (constant c) =
      ScalingLattice.coordinateEmbedding K Γ e (constant c)
    rw [KoszulLattice.latticeMap_constant, ScalingLattice.coordinateEmbedding_constant]
  · intro a
    change KoszulLattice.latticeMap K _ (monomial K a) =
      ScalingLattice.coordinateEmbedding K Γ e (monomial K a)
    rw [KoszulLattice.latticeMap_monomial, ScalingLattice.coordinateEmbedding_monomial]
    rfl

variable {p : ℕ} [Fact p.Prime]

theorem reduction_intertwines (a : Translation D →+ Translation D) (b : Translation D) :
    KoszulLattice.reducedMap (ZMod p) a (reduction p D b) = reduction p D (a b) := by
  have hb : b = ∑ i : Fin D, b i • translationBasis i := by
    ext j
    simp [translationBasis, Finset.sum_apply, Pi.single_apply]
  have hab : a b = ∑ i : Fin D, b i • a (translationBasis i) := by
    conv_lhs => rw [hb]
    simp only [map_sum, map_zsmul]
  rw [hab]
  ext j
  simp [KoszulLattice.reducedMap, Module.Basis.constr_apply_fintype,
    reduction, Finset.sum_apply, Pi.smul_apply, zsmul_eq_mul]

theorem reducedMap_range_eq_image :
    LinearMap.range (KoszulLattice.reducedMap (ZMod p) (inclusionCoordinates Γ e)) = image p D Γ := by
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    obtain ⟨b, rfl⟩ := reduction_surjective p D w
    rw [reduction_intertwines]
    exact ⟨e.symm b, (e.symm b).property, rfl⟩
  · rintro ⟨b, hb, rfl⟩
    refine ⟨reduction p D (e ⟨b, hb⟩), ?_⟩
    rw [reduction_intertwines]
    simp

variable {M : Type*} [AddCommGroup M] [Module (ZMod p) M] {n : ℕ}

/-- Composition with the actual reduced inclusion is zero exactly when
the alternating form vanishes on every tuple from the image subspace. -/
theorem comp_reducedMap_zero_iff
    (f : AlternatingMap (ZMod p) (Residue p D) M (Fin n)) :
    f.compLinearMap (KoszulLattice.reducedMap (ZMod p) (inclusionCoordinates Γ e)) = 0 ↔
      ∀ v : Fin n → Residue p D, (∀ i, v i ∈ image p D Γ) → f v = 0 := by
  rw [← reducedMap_range_eq_image Γ e]
  constructor
  · intro h v hv
    choose w hw using hv
    have hh := DFunLike.congr_fun h w
    simpa only [AlternatingMap.compLinearMap_apply, hw, AlternatingMap.zero_apply] using hh
  · intro h
    ext v
    exact h _ (fun i => ⟨v i, rfl⟩)

end
end Decoupling.HighDim.MinimalLattice
